/* tc-arc.c -- Assembler for the ARC
   Copyright (C) 1994-2025 Free Software Foundation, Inc.

   Contributor: Claudiu Zissulescu <claziss@synopsys.com>

   This file is part of GAS, the GNU Assembler.

   GAS is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3, or (at your option)
   any later version.

   GAS is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with GAS; see the file COPYING.  If not, write to the Free
   Software Foundation, 51 Franklin Street - Fifth Floor, Boston, MA
   02110-1301, USA.  */

#include "as.h"
#include "subsegs.h"
#include "dwarf2dbg.h"
#include "dw2gencfi.h"
#include "safe-ctype.h"

#include "opcode/arc.h"
#include "opcode/arc-attrs.h"
#include "elf/arc.h"
#include "../opcodes/arc-ext.h"

/* Defines section.  */

#define MAX_INSN_FIXUPS      2
#define MAX_CONSTR_STR       20
#define FRAG_MAX_GROWTH      8

#ifdef DEBUG
# define pr_debug(fmt, args...) fprintf (stderr, fmt, ##args)
#else
# define pr_debug(fmt, args...)
#endif

#define MAJOR_OPCODE(x)  (((x) & 0xF8000000) >> 27)
#define SUB_OPCODE(x)	 (((x) & 0x003F0000) >> 16)
#define LP_INSN(x)	 ((MAJOR_OPCODE (x) == 0x4) \
			  && (SUB_OPCODE (x) == 0x28))

#ifndef TARGET_WITH_CPU
#define TARGET_WITH_CPU "hs38_linux"
#endif /* TARGET_WITH_CPU */

#define ARC_GET_FLAG(s)   	(*symbol_get_tc (s))
#define ARC_SET_FLAG(s,v) 	(*symbol_get_tc (s) |= (v))
#define streq(a, b)	      (strcmp (a, b) == 0)

/* Enum used to enumerate the relaxable ins operands.  */
enum rlx_operand_type
{
  EMPTY = 0,
  REGISTER,
  REGISTER_S,     /* Register for short instruction(s).  */
  REGISTER_NO_GP, /* Is a register but not gp register specifically.  */
  REGISTER_DUP,   /* Duplication of previous operand of type register.  */
  IMMEDIATE,
  BRACKET
};

enum arc_rlx_types
{
  ARC_RLX_NONE = 0,
  ARC_RLX_BL_S,
  ARC_RLX_BL,
  ARC_RLX_B_S,
  ARC_RLX_B,
  ARC_RLX_ADD_U3,
  ARC_RLX_ADD_U6,
  ARC_RLX_ADD_LIMM,
  ARC_RLX_LD_U7,
  ARC_RLX_LD_S9,
  ARC_RLX_LD_LIMM,
  ARC_RLX_MOV_U8,
  ARC_RLX_MOV_S12,
  ARC_RLX_MOV_LIMM,
  ARC_RLX_SUB_U3,
  ARC_RLX_SUB_U6,
  ARC_RLX_SUB_LIMM,
  ARC_RLX_MPY_U6,
  ARC_RLX_MPY_LIMM,
  ARC_RLX_MOV_RU6,
  ARC_RLX_MOV_RLIMM,
  ARC_RLX_ADD_RRU6,
  ARC_RLX_ADD_RRLIMM,
};

/* Macros section.  */

#define regno(x)		((x) & 0x3F)
#define is_ir_num(x)		(((x) & ~0x3F) == 0)
#define is_code_density_p(sc)   (((sc) == CD1 || (sc) == CD2))
#define is_spfp_p(op)           (((sc) == SPX))
#define is_dpfp_p(op)           (((sc) == DPX))
#define is_fpuda_p(op)          (((sc) == DPA))
#define is_br_jmp_insn_p(op)    (((op)->insn_class == BRANCH		\
				  || (op)->insn_class == JUMP		\
				  || (op)->insn_class == BRCC		\
				  || (op)->insn_class == BBIT0		\
				  || (op)->insn_class == BBIT1		\
				  || (op)->insn_class == BI		\
				  || (op)->insn_class == DBNZ		\
				  || (op)->insn_class == EI		\
				  || (op)->insn_class == ENTER		\
				  || (op)->insn_class == JLI		\
				  || (op)->insn_class == LOOP		\
				  || (op)->insn_class == LEAVE		\
				  ))
#define is_kernel_insn_p(op)    (((op)->insn_class == KERNEL))
#define is_nps400_p(op)         (((sc) == NPS400))

/* Generic assembler global variables which must be defined by all
   targets.  */

/* Characters which always start a comment.  */
const char comment_chars[] = "#;";

/* Characters which start a comment at the beginning of a line.  */
const char line_comment_chars[] = "#";

/* Characters which may be used to separate multiple commands on a
   single line.  */
const char line_separator_chars[] = "`";

/* Characters which are used to indicate an exponent in a floating
   point number.  */
const char EXP_CHARS[] = "eE";

/* Chars that mean this number is a floating point constant
   As in 0f12.456 or 0d1.2345e12.  */
const char FLT_CHARS[] = "rRsSfFdD";

/* Byte order.  */
extern int target_big_endian;
const char *arc_target_format = DEFAULT_TARGET_FORMAT;
static int byte_order = DEFAULT_BYTE_ORDER;

/* Arc extension section.  */
static segT arcext_section;

/* By default relaxation is disabled.  */
static int relaxation_state = 0;

extern int arc_get_mach (char *);

/* Forward declarations.  */
static void arc_lcomm (int);
static void arc_option (int);
static void arc_extra_reloc (int);
static void arc_extinsn (int);
static void arc_extcorereg (int);
static void arc_attribute (int);

const pseudo_typeS md_pseudo_table[] =
{
  /* Make sure that .word is 32 bits.  */
  { "word", cons, 4 },

  { "align",   s_align_bytes, 0 }, /* Defaulting is invalid (0).  */
  { "lcomm",   arc_lcomm, 0 },
  { "lcommon", arc_lcomm, 0 },
  { "cpu",     arc_option, 0 },

  { "arc_attribute",   arc_attribute, 0 },
  { "extinstruction",  arc_extinsn, 0 },
  { "extcoreregister", arc_extcorereg, EXT_CORE_REGISTER },
  { "extauxregister",  arc_extcorereg, EXT_AUX_REGISTER },
  { "extcondcode",     arc_extcorereg, EXT_COND_CODE },

  { "tls_gd_ld",   arc_extra_reloc, BFD_RELOC_ARC_TLS_GD_LD },
  { "tls_gd_call", arc_extra_reloc, BFD_RELOC_ARC_TLS_GD_CALL },

  { NULL, NULL, 0 }
};

const char md_shortopts[] = "";

enum options
{
  OPTION_EB = OPTION_MD_BASE,
  OPTION_EL,

  OPTION_ARC600,
  OPTION_ARC601,
  OPTION_ARC700,
  OPTION_ARCEM,
  OPTION_ARCHS,

  OPTION_MCPU,
  OPTION_CD,
  OPTION_RELAX,
  OPTION_NPS400,

  OPTION_SPFP,
  OPTION_DPFP,
  OPTION_FPUDA,

  /* The following options are deprecated and provided here only for
     compatibility reasons.  */
  OPTION_USER_MODE,
  OPTION_LD_EXT_MASK,
  OPTION_SWAP,
  OPTION_NORM,
  OPTION_BARREL_SHIFT,
  OPTION_MIN_MAX,
  OPTION_NO_MPY,
  OPTION_EA,
  OPTION_MUL64,
  OPTION_SIMD,
  OPTION_XMAC_D16,
  OPTION_XMAC_24,
  OPTION_DSP_PACKA,
  OPTION_CRC,
  OPTION_DVBF,
  OPTION_TELEPHONY,
  OPTION_XYMEMORY,
  OPTION_LOCK,
  OPTION_SWAPE,
  OPTION_RTSC
};

const struct option md_longopts[] =
{
  { "EB",		no_argument,	   NULL, OPTION_EB },
  { "EL",		no_argument,	   NULL, OPTION_EL },
  { "mcpu",		required_argument, NULL, OPTION_MCPU },
  { "mA6",		no_argument,	   NULL, OPTION_ARC600 },
  { "mARC600",		no_argument,	   NULL, OPTION_ARC600 },
  { "mARC601",		no_argument,	   NULL, OPTION_ARC601 },
  { "mARC700",		no_argument,	   NULL, OPTION_ARC700 },
  { "mA7",		no_argument,	   NULL, OPTION_ARC700 },
  { "mEM",		no_argument,	   NULL, OPTION_ARCEM },
  { "mHS",		no_argument,	   NULL, OPTION_ARCHS },
  { "mcode-density",	no_argument,	   NULL, OPTION_CD },
  { "mrelax",           no_argument,       NULL, OPTION_RELAX },
  { "mnps400",          no_argument,       NULL, OPTION_NPS400 },

  /* Floating point options */
  { "mspfp", no_argument, NULL, OPTION_SPFP},
  { "mspfp-compact", no_argument, NULL, OPTION_SPFP},
  { "mspfp_compact", no_argument, NULL, OPTION_SPFP},
  { "mspfp-fast", no_argument, NULL, OPTION_SPFP},
  { "mspfp_fast", no_argument, NULL, OPTION_SPFP},
  { "mdpfp", no_argument, NULL, OPTION_DPFP},
  { "mdpfp-compact", no_argument, NULL, OPTION_DPFP},
  { "mdpfp_compact", no_argument, NULL, OPTION_DPFP},
  { "mdpfp-fast", no_argument, NULL, OPTION_DPFP},
  { "mdpfp_fast", no_argument, NULL, OPTION_DPFP},
  { "mfpuda", no_argument, NULL, OPTION_FPUDA},

  /* The following options are deprecated and provided here only for
     compatibility reasons.  */
  { "mav2em", no_argument, NULL, OPTION_ARCEM },
  { "mav2hs", no_argument, NULL, OPTION_ARCHS },
  { "muser-mode-only", no_argument, NULL, OPTION_USER_MODE },
  { "mld-extension-reg-mask", required_argument, NULL, OPTION_LD_EXT_MASK },
  { "mswap", no_argument, NULL, OPTION_SWAP },
  { "mnorm", no_argument, NULL, OPTION_NORM },
  { "mbarrel-shifter", no_argument, NULL, OPTION_BARREL_SHIFT },
  { "mbarrel_shifter", no_argument, NULL, OPTION_BARREL_SHIFT },
  { "mmin-max", no_argument, NULL, OPTION_MIN_MAX },
  { "mmin_max", no_argument, NULL, OPTION_MIN_MAX },
  { "mno-mpy", no_argument, NULL, OPTION_NO_MPY },
  { "mea", no_argument, NULL, OPTION_EA },
  { "mEA", no_argument, NULL, OPTION_EA },
  { "mmul64", no_argument, NULL, OPTION_MUL64 },
  { "msimd", no_argument, NULL, OPTION_SIMD},
  { "mmac-d16", no_argument, NULL, OPTION_XMAC_D16},
  { "mmac_d16", no_argument, NULL, OPTION_XMAC_D16},
  { "mmac-24", no_argument, NULL, OPTION_XMAC_24},
  { "mmac_24", no_argument, NULL, OPTION_XMAC_24},
  { "mdsp-packa", no_argument, NULL, OPTION_DSP_PACKA},
  { "mdsp_packa", no_argument, NULL, OPTION_DSP_PACKA},
  { "mcrc", no_argument, NULL, OPTION_CRC},
  { "mdvbf", no_argument, NULL, OPTION_DVBF},
  { "mtelephony", no_argument, NULL, OPTION_TELEPHONY},
  { "mxy", no_argument, NULL, OPTION_XYMEMORY},
  { "mlock", no_argument, NULL, OPTION_LOCK},
  { "mswape", no_argument, NULL, OPTION_SWAPE},
  { "mrtsc", no_argument, NULL, OPTION_RTSC},

  { NULL,		no_argument, NULL, 0 }
};

const size_t md_longopts_size = sizeof (md_longopts);

/* Local data and data types.  */

/* Used since new relocation types are introduced in this
   file (DUMMY_RELOC_LITUSE_*).  */
typedef int extended_bfd_reloc_code_real_type;

struct arc_fixup
{
  expressionS exp;

  extended_bfd_reloc_code_real_type reloc;

  /* index into arc_operands.  */
  unsigned int opindex;

  /* PC-relative, used by internals fixups.  */
  unsigned char pcrel;

  /* TRUE if this fixup is for LIMM operand.  */
  bool islong;
};

struct arc_insn
{
  unsigned long long int insn;
  int nfixups;
  struct arc_fixup fixups[MAX_INSN_FIXUPS];
  long limm;
  unsigned int len;     /* Length of instruction in bytes.  */
  bool has_limm;	/* Boolean value: TRUE if limm field is valid.  */
  bool relax;		/* Boolean value: TRUE if needs relaxation.  */
};

/* Structure to hold any last two instructions.  */
static struct arc_last_insn
{
  /* Saved instruction opcode.  */
  const struct arc_opcode *opcode;

  /* Boolean value: TRUE if current insn is short.  */
  bool has_limm;

  /* Boolean value: TRUE if current insn has delay slot.  */
  bool has_delay_slot;
} arc_last_insns[2];

/* Extension instruction suffix classes.  */
typedef struct
{
  const char *name;
  int  len;
  int  attr_class;
} attributes_t;

static const attributes_t suffixclass[] =
{
  { "SUFFIX_FLAG", 11, ARC_SUFFIX_FLAG },
  { "SUFFIX_COND", 11, ARC_SUFFIX_COND },
  { "SUFFIX_NONE", 11, ARC_SUFFIX_NONE }
};

/* Extension instruction syntax classes.  */
static const attributes_t syntaxclass[] =
{
  { "SYNTAX_3OP", 10, ARC_SYNTAX_3OP },
  { "SYNTAX_2OP", 10, ARC_SYNTAX_2OP },
  { "SYNTAX_1OP", 10, ARC_SYNTAX_1OP },
  { "SYNTAX_NOP", 10, ARC_SYNTAX_NOP }
};

/* Extension instruction syntax classes modifiers.  */
static const attributes_t syntaxclassmod[] =
{
  { "OP1_IMM_IMPLIED" , 15, ARC_OP1_IMM_IMPLIED },
  { "OP1_MUST_BE_IMM" , 15, ARC_OP1_MUST_BE_IMM }
};

/* Extension register type.  */
typedef struct
{
  char *name;
  int  number;
  int  imode;
} extRegister_t;

/* A structure to hold the additional conditional codes.  */
static struct
{
  struct arc_flag_operand *arc_ext_condcode;
  int size;
} ext_condcode = { NULL, 0 };

/* Structure to hold an entry in ARC_OPCODE_HASH.  */
struct arc_opcode_hash_entry
{
  /* The number of pointers in the OPCODE list.  */
  size_t count;

  /* Points to a list of opcode pointers.  */
  const struct arc_opcode **opcode;
};

/* Structure used for iterating through an arc_opcode_hash_entry.  */
struct arc_opcode_hash_entry_iterator
{
  /* Index into the OPCODE element of the arc_opcode_hash_entry.  */
  size_t index;

  /* The specific ARC_OPCODE from the ARC_OPCODES table that was last
     returned by this iterator.  */
  const struct arc_opcode *opcode;
};

/* Forward declaration.  */
static void assemble_insn
  (const struct arc_opcode *, const expressionS *, int,
   const struct arc_flags *, int, struct arc_insn *);

/* The selection of the machine type can come from different sources.  This
   enum is used to track how the selection was made in order to perform
   error checks.  */
enum mach_selection_type
  {
    MACH_SELECTION_NONE,
    MACH_SELECTION_FROM_DEFAULT,
    MACH_SELECTION_FROM_CPU_DIRECTIVE,
    MACH_SELECTION_FROM_COMMAND_LINE
  };

/* How the current machine type was selected.  */
static enum mach_selection_type mach_selection_mode = MACH_SELECTION_NONE;

/* The hash table of instruction opcodes.  */
static htab_t arc_opcode_hash;

/* The hash table of register symbols.  */
static htab_t arc_reg_hash;

/* The hash table of aux register symbols.  */
static htab_t arc_aux_hash;

/* The hash table of address types.  */
static htab_t arc_addrtype_hash;

#define ARC_CPU_TYPE_A6xx(NAME,EXTRA)			\
  { #NAME, ARC_OPCODE_ARC600, bfd_mach_arc_arc600,	\
      E_ARC_MACH_ARC600, EXTRA}
#define ARC_CPU_TYPE_A7xx(NAME,EXTRA)			\
  { #NAME, ARC_OPCODE_ARC700,  bfd_mach_arc_arc700,	\
      E_ARC_MACH_ARC700, EXTRA}
#define ARC_CPU_TYPE_AV2EM(NAME,EXTRA)			\
  { #NAME,  ARC_OPCODE_ARCv2EM, bfd_mach_arc_arcv2,	\
      EF_ARC_CPU_ARCV2EM, EXTRA}
#define ARC_CPU_TYPE_AV2HS(NAME,EXTRA)			\
  { #NAME,  ARC_OPCODE_ARCv2HS, bfd_mach_arc_arcv2,	\
      EF_ARC_CPU_ARCV2HS, EXTRA}
#define ARC_CPU_TYPE_NONE				\
  { 0, 0, 0, 0, 0 }

/* A table of CPU names and opcode sets.  */
static const struct cpu_type
{
  const char *name;
  unsigned flags;
  int mach;
  unsigned eflags;
  unsigned features;
}
  cpu_types[] =
{
  #include "elf/arc-cpu.def"
};

/* Information about the cpu/variant we're assembling for.  */
static struct cpu_type selected_cpu = { 0, 0, 0, E_ARC_OSABI_CURRENT, 0 };

/* TRUE if current assembly code uses RF16 only registers.  */
static bool rf16_only = true;

/* MPY option.  */
static unsigned mpy_option = 0;

/* Use PIC. */
static unsigned pic_option = 0;

/* Use small data.  */
static unsigned sda_option = 0;

/* Use TLS.  */
static unsigned tls_option = 0;

/* Command line given features.  */
static unsigned cl_features = 0;

/* Used by the arc_reloc_op table.  Order is important.  */
#define O_gotoff  O_md1     /* @gotoff relocation.  */
#define O_gotpc   O_md2     /* @gotpc relocation.  */
#define O_plt     O_md3     /* @plt relocation.  */
#define O_sda     O_md4     /* @sda relocation.  */
#define O_pcl     O_md5     /* @pcl relocation.  */
#define O_tlsgd   O_md6     /* @tlsgd relocation.  */
#define O_tlsie   O_md7     /* @tlsie relocation.  */
#define O_tpoff9  O_md8     /* @tpoff9 relocation.  */
#define O_tpoff   O_md9     /* @tpoff relocation.  */
#define O_dtpoff9 O_md10    /* @dtpoff9 relocation.  */
#define O_dtpoff  O_md11    /* @dtpoff relocation.  */
#define O_last    O_dtpoff

/* Used to define a bracket as operand in tokens.  */
#define O_bracket O_md32

/* Used to define a colon as an operand in tokens.  */
#define O_colon O_md31

/* Used to define address types in nps400.  */
#define O_addrtype O_md30

/* Dummy relocation, to be sorted out.  */
#define DUMMY_RELOC_ARC_ENTRY     (BFD_RELOC_UNUSED + 1)

#define USER_RELOC_P(R) ((R) >= O_gotoff && (R) <= O_last)

/* A table to map the spelling of a relocation operand into an appropriate
   bfd_reloc_code_real_type type.  The table is assumed to be ordered such
   that op-O_literal indexes into it.  */
#define ARC_RELOC_TABLE(op)				\
  (&arc_reloc_op[ ((!USER_RELOC_P (op))			\
		   ? (abort (), 0)			\
		   : (op) - O_gotoff) ])

#define DEF(NAME, RELOC, REQ)				\
  { #NAME, sizeof (#NAME)-1, O_##NAME, RELOC, REQ}

static const struct arc_reloc_op_tag
{
  /* String to lookup.  */
  const char *name;
  /* Size of the string.  */
  size_t length;
  /* Which operator to use.  */
  operatorT op;
  extended_bfd_reloc_code_real_type reloc;
  /* Allows complex relocation expression like identifier@reloc +
     const.  */
  unsigned int complex_expr : 1;
}
  arc_reloc_op[] =
{
  DEF (gotoff,  BFD_RELOC_ARC_GOTOFF,		1),
  DEF (gotpc,   BFD_RELOC_ARC_GOTPC32,		0),
  DEF (plt,	BFD_RELOC_ARC_PLT32,		0),
  DEF (sda,	DUMMY_RELOC_ARC_ENTRY,		1),
  DEF (pcl,	BFD_RELOC_ARC_PC32,		1),
  DEF (tlsgd,   BFD_RELOC_ARC_TLS_GD_GOT,	0),
  DEF (tlsie,   BFD_RELOC_ARC_TLS_IE_GOT,	0),
  DEF (tpoff9,  BFD_RELOC_ARC_TLS_LE_S9,	0),
  DEF (tpoff,   BFD_RELOC_ARC_TLS_LE_32,	1),
  DEF (dtpoff9, BFD_RELOC_ARC_TLS_DTPOFF_S9,	0),
  DEF (dtpoff,  BFD_RELOC_ARC_TLS_DTPOFF,	1),
};

static const int arc_num_reloc_op
= sizeof (arc_reloc_op) / sizeof (*arc_reloc_op);

/* Structure for relaxable instruction that have to be swapped with a
   smaller alternative instruction.  */
struct arc_relaxable_ins
{
  /* Mnemonic that should be checked.  */
  const char *mnemonic_r;

  /* Operands that should be checked.
     Indexes of operands from operand array.  */
  enum rlx_operand_type operands[6];

  /* Flags that should be checked.  */
  unsigned flag_classes[5];

  /* Mnemonic (smaller) alternative to be used later for relaxation.  */
  const char *mnemonic_alt;

  /* Index of operand that generic relaxation has to check.  */
  unsigned opcheckidx;

  /* Base subtype index used.  */
  enum arc_rlx_types subtype;
};

#define RELAX_TABLE_ENTRY(BITS, ISSIGNED, SIZE, NEXT)			\
  { (ISSIGNED) ? ((1 << ((BITS) - 1)) - 1) : ((1 << (BITS)) - 1),	\
      (ISSIGNED) ? -(1 << ((BITS) - 1)) : 0,				\
      (SIZE),								\
      (NEXT) }								\

#define RELAX_TABLE_ENTRY_MAX(ISSIGNED, SIZE, NEXT)	\
  { (ISSIGNED) ? 0x7FFFFFFF : 0xFFFFFFFF,		\
      (ISSIGNED) ? -(0x7FFFFFFF) : 0,                   \
      (SIZE),                                           \
      (NEXT) }                                          \


/* ARC relaxation table.  */
const relax_typeS md_relax_table[] =
{
  /* Fake entry.  */
  {0, 0, 0, 0},

  /* BL_S s13 ->
     BL s25.  */
  RELAX_TABLE_ENTRY (13, 1, 2, ARC_RLX_BL),
  RELAX_TABLE_ENTRY (25, 1, 4, ARC_RLX_NONE),

  /* B_S s10 ->
     B s25.  */
  RELAX_TABLE_ENTRY (10, 1, 2, ARC_RLX_B),
  RELAX_TABLE_ENTRY (25, 1, 4, ARC_RLX_NONE),

  /* ADD_S c,b, u3 ->
     ADD<.f> a,b,u6 ->
     ADD<.f> a,b,limm.  */
  RELAX_TABLE_ENTRY (3, 0, 2, ARC_RLX_ADD_U6),
  RELAX_TABLE_ENTRY (6, 0, 4, ARC_RLX_ADD_LIMM),
  RELAX_TABLE_ENTRY_MAX (0, 8, ARC_RLX_NONE),

  /* LD_S a, [b, u7] ->
     LD<zz><.x><.aa><.di> a, [b, s9] ->
     LD<zz><.x><.aa><.di> a, [b, limm] */
  RELAX_TABLE_ENTRY (7, 0, 2, ARC_RLX_LD_S9),
  RELAX_TABLE_ENTRY (9, 1, 4, ARC_RLX_LD_LIMM),
  RELAX_TABLE_ENTRY_MAX (1, 8, ARC_RLX_NONE),

  /* MOV_S b, u8 ->
     MOV<.f> b, s12 ->
     MOV<.f> b, limm.  */
  RELAX_TABLE_ENTRY (8, 0, 2, ARC_RLX_MOV_S12),
  RELAX_TABLE_ENTRY (8, 0, 4, ARC_RLX_MOV_LIMM),
  RELAX_TABLE_ENTRY_MAX (0, 8, ARC_RLX_NONE),

  /* SUB_S c, b, u3 ->
     SUB<.f> a, b, u6 ->
     SUB<.f> a, b, limm.  */
  RELAX_TABLE_ENTRY (3, 0, 2, ARC_RLX_SUB_U6),
  RELAX_TABLE_ENTRY (6, 0, 4, ARC_RLX_SUB_LIMM),
  RELAX_TABLE_ENTRY_MAX (0, 8, ARC_RLX_NONE),

  /* MPY<.f> a, b, u6 ->
     MPY<.f> a, b, limm.  */
  RELAX_TABLE_ENTRY (6, 0, 4, ARC_RLX_MPY_LIMM),
  RELAX_TABLE_ENTRY_MAX (0, 8, ARC_RLX_NONE),

  /* MOV<.f><.cc> b, u6 ->
     MOV<.f><.cc> b, limm.  */
  RELAX_TABLE_ENTRY (6, 0, 4, ARC_RLX_MOV_RLIMM),
  RELAX_TABLE_ENTRY_MAX (0, 8, ARC_RLX_NONE),

  /* ADD<.f><.cc> b, b, u6 ->
     ADD<.f><.cc> b, b, limm.  */
  RELAX_TABLE_ENTRY (6, 0, 4, ARC_RLX_ADD_RRLIMM),
  RELAX_TABLE_ENTRY_MAX (0, 8, ARC_RLX_NONE),
};

/* Order of this table's entries matters!  */
const struct arc_relaxable_ins arc_relaxable_insns[] =
{
  { "bl", { IMMEDIATE }, { 0 }, "bl_s", 0, ARC_RLX_BL_S },
  { "b", { IMMEDIATE }, { 0 }, "b_s", 0, ARC_RLX_B_S },
  { "add", { REGISTER, REGISTER_DUP, IMMEDIATE }, { 5, 1, 0 }, "add",
    2, ARC_RLX_ADD_RRU6},
  { "add", { REGISTER_S, REGISTER_S, IMMEDIATE }, { 0 }, "add_s", 2,
    ARC_RLX_ADD_U3 },
  { "add", { REGISTER, REGISTER, IMMEDIATE }, { 5, 0 }, "add", 2,
    ARC_RLX_ADD_U6 },
  { "ld", { REGISTER_S, BRACKET, REGISTER_S, IMMEDIATE, BRACKET },
    { 0 }, "ld_s", 3, ARC_RLX_LD_U7 },
  { "ld", { REGISTER, BRACKET, REGISTER_NO_GP, IMMEDIATE, BRACKET },
    { 11, 4, 14, 17, 0 }, "ld", 3, ARC_RLX_LD_S9 },
  { "mov", { REGISTER_S, IMMEDIATE }, { 0 }, "mov_s", 1, ARC_RLX_MOV_U8 },
  { "mov", { REGISTER, IMMEDIATE }, { 5, 0 }, "mov", 1, ARC_RLX_MOV_S12 },
  { "mov", { REGISTER, IMMEDIATE }, { 5, 1, 0 },"mov", 1, ARC_RLX_MOV_RU6 },
  { "sub", { REGISTER_S, REGISTER_S, IMMEDIATE }, { 0 }, "sub_s", 2,
    ARC_RLX_SUB_U3 },
  { "sub", { REGISTER, REGISTER, IMMEDIATE }, { 5, 0 }, "sub", 2,
    ARC_RLX_SUB_U6 },
  { "mpy", { REGISTER, REGISTER, IMMEDIATE }, { 5, 0 }, "mpy", 2,
    ARC_RLX_MPY_U6 },
};

const unsigned arc_num_relaxable_ins = ARRAY_SIZE (arc_relaxable_insns);

/* Pre-defined "_GLOBAL_OFFSET_TABLE_".  */
symbolS * GOT_symbol = 0;

/* Set to TRUE when we assemble instructions.  */
static bool assembling_insn = false;

/* List with attributes set explicitly.  */
static bool attributes_set_explicitly[NUM_KNOWN_OBJ_ATTRIBUTES];

/* Functions implementation.  */

/* Return a pointer to ARC_OPCODE_HASH_ENTRY that identifies all
   ARC_OPCODE entries in ARC_OPCODE_HASH that match NAME, or NULL if there
   are no matching entries in ARC_OPCODE_HASH.  */

static const struct arc_opcode_hash_entry *
arc_find_opcode (const char *name)
{
  if (!name)
    {
      return NULL;
    }
  return str_hash_find (arc_opcode_hash, name);
}

/* Initialise the iterator ITER.  */

static void
arc_opcode_hash_entry_iterator_init (struct arc_opcode_hash_entry_iterator *iter)
{
  if (!iter)
    {
      return;
    }

  iter->index = 0;
  iter->opcode = NULL;
}

/* Return the next ARC_OPCODE from ENTRY, using ITER to hold state between
   calls to this function.  Return NULL when all ARC_OPCODE entries have
   been returned.  */

static const struct arc_opcode *
arc_opcode_hash_entry_iterator_next (const struct arc_opcode_hash_entry *entry,
				     struct arc_opcode_hash_entry_iterator *iter)
{
  if (iter->opcode == NULL && iter->index == 0)
    {
      gas_assert (entry->count > 0);
      iter->opcode = entry->opcode[0];
    }
  else if (iter->opcode != NULL)
    {
      const char *old_name = iter->opcode->name;
      iter->opcode++;

      if (iter->opcode->name == NULL
	  || strcmp (old_name, iter->opcode->name) != 0)
	{
	  iter->index++;
	  iter->opcode = (iter->index < entry->count)
	    ? entry->opcode[iter->index] : NULL;
	}
    }

  return iter->opcode;
}

/* Insert an opcode into opcode hash structure.  */

static void
arc_insert_opcode (const struct arc_opcode *opcode)
{
  const char *name = opcode->name;
  struct arc_opcode_hash_entry *entry = str_hash_find (arc_opcode_hash, name);

  if (entry == NULL)
    {
      entry = XNEW (struct arc_opcode_hash_entry);
      entry->count = 0;
      entry->opcode = NULL;

      if (str_hash_insert (arc_opcode_hash, name, entry, 0) != NULL)
        {
          as_fatal (_("internal error: hash already contains %s"), name);
        }
    }

  entry->opcode = XRESIZEVEC (const struct arc_opcode *, entry->opcode,
                              entry->count + 1);
  entry->opcode[entry->count] = opcode;
  entry->count++;
}

static void
arc_opcode_free (void *elt)
{
  if (elt == NULL)
    {
      return;
    }

  string_tuple_t *tuple = elt;
  struct arc_opcode_hash_entry *entry = (struct arc_opcode_hash_entry *) tuple->value;

  if (entry != NULL)
    {
      free (entry->opcode);
      free (entry);
    }

  free (tuple);
}

/* Like md_number_to_chars but for middle-endian values.  The 4-byte limm
   value, is encoded as 'middle-endian' for a little-endian target.  This
   function is used for regular 4, 6, and 8 byte instructions as well.  */

static void
md_number_to_chars_midend (char *buf, unsigned long long val, int n)
{
  switch (n)
    {
    case 2:
    case 4:
    case 6:
    case 8:
      break;
    default:
      abort ();
    }

  for (int i = n - 2; i >= 0; i -= 2)
    {
      unsigned long long chunk = (val >> (i * 8)) & 0xffff;
      md_number_to_chars (buf, chunk, 2);
      buf += 2;
    }
}

/* Check if a feature is allowed for a specific CPU.  */

static void
check_unsupported_features (void)
{
  for (size_t i = 0; i < ARRAY_SIZE (feature_list); i++)
    {
      const int feature_is_selected =
        (selected_cpu.features & feature_list[i].feature);
      const int cpu_is_incompatible =
        !(selected_cpu.flags & feature_list[i].cpus);

      if (feature_is_selected && cpu_is_incompatible)
        {
          as_bad (_("invalid %s option for %s cpu"), feature_list[i].name,
                  selected_cpu.name);
        }
    }
}

static void
check_conflicting_features (void)
{
  for (size_t i = 0; i < ARRAY_SIZE (conflict_list); i++)
    {
      const unsigned long conflict_mask = conflict_list[i];
      if ((selected_cpu.features & conflict_mask) == conflict_mask)
        {
          as_bad (_("conflicting ISA extension attributes."));
        }
    }
}

static void
arc_check_feature (void)
{
  if (!selected_cpu.features || !selected_cpu.name)
    {
      return;
    }

  check_unsupported_features ();
  check_conflicting_features ();
}

/* Select an appropriate entry from CPU_TYPES based on ARG and initialise
   the relevant static global variables.  Parameter SEL describes where
   this selection originated from.  */

static void
arc_select_cpu (const char *arg, enum mach_selection_type sel)
{
  int i;
  const struct cpu_type *found_cpu = NULL;
  static unsigned long old_mach = 0;

  gas_assert (sel != MACH_SELECTION_FROM_DEFAULT
              || mach_selection_mode == MACH_SELECTION_NONE);

  if ((mach_selection_mode == MACH_SELECTION_FROM_CPU_DIRECTIVE)
      && (sel == MACH_SELECTION_FROM_CPU_DIRECTIVE))
    {
      as_bad (_("Multiple .cpu directives found"));
    }

  for (i = 0; cpu_types[i].name; ++i)
    {
      if (!strcasecmp (cpu_types[i].name, arg))
        {
          found_cpu = &cpu_types[i];
          break;
        }
    }

  if (!found_cpu)
    {
      as_fatal (_("unknown architecture: %s\n"), arg);
    }

  if (mach_selection_mode == MACH_SELECTION_FROM_COMMAND_LINE)
    {
      gas_assert (sel == MACH_SELECTION_FROM_COMMAND_LINE
                  || sel == MACH_SELECTION_FROM_CPU_DIRECTIVE);
      if (sel == MACH_SELECTION_FROM_CPU_DIRECTIVE
          && selected_cpu.mach != found_cpu->mach)
        {
          as_warn (_("Command-line value overrides \".cpu\" directive"));
        }
      return;
    }

  selected_cpu.flags = found_cpu->flags;
  selected_cpu.name = found_cpu->name;
  selected_cpu.features = found_cpu->features | cl_features;
  selected_cpu.mach = found_cpu->mach;
  selected_cpu.eflags = (selected_cpu.eflags & ~EF_ARC_MACH_MSK)
                        | found_cpu->eflags;

  arc_check_feature ();

  if (mach_selection_mode != MACH_SELECTION_NONE
      && old_mach != selected_cpu.mach)
    {
      bfd_find_target (arc_target_format, stdoutput);
      if (!bfd_set_arch_mach (stdoutput, bfd_arch_arc, selected_cpu.mach))
        {
          as_warn (_("Could not set architecture and machine"));
        }
    }

  mach_selection_mode = sel;
  old_mach = selected_cpu.mach;
}

/* Here ends all the ARCompact extension instruction assembling
   stuff.  */

static symbolS *
parse_symbol_from_input (char *terminator_char)
{
  char *symbol_name;
  *terminator_char = get_symbol_name (&symbol_name);
  symbolS *symbol = symbol_find_or_make (symbol_name);
  restore_line_pointer (*terminator_char);
  return symbol;
}

static void
arc_extra_reloc (int r_type)
{
  char terminator;
  symbolS *sym;
  symbolS *lab = NULL;

  if (*input_line_pointer == '@')
    {
      input_line_pointer++;
    }

  sym = parse_symbol_from_input (&terminator);

  if (terminator == ',' && r_type == BFD_RELOC_ARC_TLS_GD_LD)
    {
      ++input_line_pointer;
      lab = parse_symbol_from_input (&terminator);
    }

  /* These relocations exist as a mechanism for the compiler to tell the
     linker how to patch the code if the tls model is optimised.  However,
     the relocation itself does not require any space within the assembler
     fragment, and so we pass a size of 0.

     The lines that generate these relocations look like this:

         .tls_gd_ld @.tdata`bl __tls_get_addr@plt

     The '.tls_gd_ld @.tdata' is processed first and generates the
     additional relocation, while the 'bl __tls_get_addr@plt' is processed
     second and generates the additional branch.

     It is possible that the additional relocation generated by the
     '.tls_gd_ld @.tdata' will be attached at the very end of one fragment,
     while the 'bl __tls_get_addr@plt' will be generated as the first thing
     in the next fragment.  This will be fine; both relocations will still
     appear to be at the same address in the generated object file.
     However, this only works as the additional relocation is generated
     with size of 0 bytes.  */
  fixS *fixP = fix_new (frag_now,
                       frag_now_fix (),
                       0,
                       sym,
                       0,
                       false,
                       r_type);
  fixP->fx_subsy = lab;
}

static symbolS *
arc_lcomm_internal (int ignore ATTRIBUTE_UNUSED,
		    symbolS *symbolP, addressT size)
{
  if (!symbolP)
    {
      return NULL;
    }

  addressT align;

  if (size >= 8)
    {
      align = 3;
    }
  else if (size >= 4)
    {
      align = 2;
    }
  else if (size >= 2)
    {
      align = 1;
    }
  else
    {
      align = 0;
    }

  SKIP_WHITESPACE ();

  if (*input_line_pointer == ',')
    {
      addressT parsed_align = parse_align (1);

      if (parsed_align == (addressT) -1)
	{
	  return NULL;
	}
      align = parsed_align;
    }

  bss_alloc (symbolP, size, align);
  S_CLEAR_EXTERNAL (symbolP);

  return symbolP;
}

static void
arc_lcomm (int ignore)
{
  symbolS *symbolP = s_comm_internal (ignore, arc_lcomm_internal);

  if (symbolP != NULL)
    {
      bfd_symbol *bfd_sym = symbol_get_bfdsym (symbolP);
      if (bfd_sym != NULL)
        {
          bfd_sym->flags |= BSF_OBJECT;
        }
    }
}

/* Select the cpu we're assembling for.  */

static void
arc_option (int ignore ATTRIBUTE_UNUSED)
{
  char c;
  char *cpu;
  const char *cpu_name;

  struct cpu_map
  {
    const char *const alias;
    const char *const canonical;
  };

  static const struct cpu_map cpu_mappings[] = {
    {"ARC600", "arc600"},
    {"ARC601", "arc600"},
    {"A6", "arc600"},
    {"ARC700", "arc700"},
    {"A7", "arc700"},
    {"EM", "arcem"},
    {"HS", "archs"},
    {"NPS400", "nps400"},
  };

  c = get_symbol_name (&cpu);
  cpu_name = cpu;

  for (size_t i = 0; i < sizeof (cpu_mappings) / sizeof (cpu_mappings[0]); ++i)
    {
      if (strcmp (cpu_mappings[i].alias, cpu) == 0)
        {
          cpu_name = cpu_mappings[i].canonical;
          break;
        }
    }

  arc_select_cpu (cpu_name, MACH_SELECTION_FROM_CPU_DIRECTIVE);

  restore_line_pointer (c);
  demand_empty_rest_of_line ();
}

/* Smartly print an expression.  */

static const char * const op_names[] = {
  [O_illegal] = "O_illegal",
  [O_absent] = "O_absent",
  [O_constant] = "O_constant",
  [O_symbol] = "O_symbol",
  [O_symbol_rva] = "O_symbol_rva",
  [O_register] = "O_register",
  [O_big] = "O_big",
  [O_uminus] = "O_uminus",
  [O_bit_not] = "O_bit_not",
  [O_logical_not] = "O_logical_not",
  [O_multiply] = "O_multiply",
  [O_divide] = "O_divide",
  [O_modulus] = "O_modulus",
  [O_left_shift] = "O_left_shift",
  [O_right_shift] = "O_right_shift",
  [O_bit_inclusive_or] = "O_bit_inclusive_or",
  [O_bit_or_not] = "O_bit_or_not",
  [O_bit_exclusive_or] = "O_bit_exclusive_or",
  [O_bit_and] = "O_bit_and",
  [O_add] = "O_add",
  [O_subtract] = "O_subtract",
  [O_eq] = "O_eq",
  [O_ne] = "O_ne",
  [O_lt] = "O_lt",
  [O_le] = "O_le",
  [O_ge] = "O_ge",
  [O_gt] = "O_gt",
  [O_logical_and] = "O_logical_and",
  [O_logical_or] = "O_logical_or",
  [O_index] = "O_index",
  [O_bracket] = "O_bracket",
  [O_colon] = "O_colon",
  [O_addrtype] = "O_addrtype"
};

static const char * const md_names[] = {
  [O_gotoff] = "O_gotoff",
  [O_gotpc] = "O_gotpc",
  [O_plt] = "O_plt",
  [O_sda] = "O_sda",
  [O_pcl] = "O_pcl",
  [O_tlsgd] = "O_tlsgd",
  [O_tlsie] = "O_tlsie",
  [O_tpoff9] = "O_tpoff9",
  [O_tpoff] = "O_tpoff",
  [O_dtpoff9] = "O_dtpoff9",
  [O_dtpoff] = "O_dtpoff"
};

static void
debug_exp (expressionS *t)
{
  const char *name ATTRIBUTE_UNUSED = "unknown";
  const char *namemd ATTRIBUTE_UNUSED = "unknown";

  pr_debug ("debug_exp: ");

  if ((unsigned) t->X_op < sizeof (op_names) / sizeof (op_names[0])
      && op_names[t->X_op])
    name = op_names[t->X_op];

  if ((unsigned) t->X_md < sizeof (md_names) / sizeof (md_names[0])
      && md_names[t->X_md])
    namemd = md_names[t->X_md];

  pr_debug ("%s (%s, %s, %d, %s)", name,
	    (t->X_add_symbol) ? S_GET_NAME (t->X_add_symbol) : "--",
	    (t->X_op_symbol) ? S_GET_NAME (t->X_op_symbol) : "--",
	    (int) t->X_add_number,
	    (t->X_md) ? namemd : "--");
  pr_debug ("\n");
  fflush (stderr);
}

/* Helper for parsing an argument, used for sorting out the relocation
   type.  */

static void
parse_reloc_symbol (expressionS *resultP)
{
  char *reloc_name, c, *sym_name;
  size_t len;
  int i;
  const struct arc_reloc_op_tag *r = NULL;
  expressionS right;
  symbolS *base;

  if (resultP->X_op != O_symbol)
    {
      as_bad (_("No valid label relocation operand"));
      resultP->X_op = O_illegal;
      return;
    }

  input_line_pointer++;
  c = get_symbol_name (&reloc_name);
  len = input_line_pointer - reloc_name;
  if (len == 0)
    {
      as_bad (_("No relocation operand"));
      resultP->X_op = O_illegal;
      return;
    }

  for (i = 0; i < arc_num_reloc_op; i++)
    {
      if (len == arc_reloc_op[i].length
	  && memcmp (reloc_name, arc_reloc_op[i].name, len) == 0)
	{
	  r = &arc_reloc_op[i];
	  break;
	}
    }

  if (r == NULL)
    {
      as_bad (_("Unknown relocation operand: @%s"), reloc_name);
      resultP->X_op = O_illegal;
      return;
    }

  restore_line_pointer (c);
  SKIP_WHITESPACE ();

  if (*input_line_pointer == '@')
    {
      if (resultP->X_op_symbol != NULL)
	{
	  as_bad (_("Unable to parse TLS base on a complex expression: %s"),
		  input_line_pointer);
	  resultP->X_op = O_illegal;
	  return;
	}

      input_line_pointer++;
      c = get_symbol_name (&sym_name);
      base = symbol_find_or_make (sym_name);
      resultP->X_op = O_subtract;
      resultP->X_op_symbol = base;
      restore_line_pointer (c);
    }

  right.X_add_number = 0;
  if (*input_line_pointer == '+' || *input_line_pointer == '-')
    {
      if (!r->complex_expr)
	{
	  as_bad (_("@%s is not a complex relocation."), r->name);
	  resultP->X_op = O_illegal;
	  return;
	}

      expression (&right);
      if (right.X_op != O_constant)
	{
	  as_bad (_("Bad expression following relocation operand."));
	  resultP->X_op = O_illegal;
	  return;
	}
    }

  resultP->X_md = r->op;
  resultP->X_add_number = right.X_add_number;
}

/* Parse the arguments to an opcode.  */

static int
tokenize_arguments (char *str,
		    expressionS *tok,
		    int ntok)
{
  char *old_input_line_pointer;
  bool saw_comma = false;
  bool saw_arg = false;
  int brk_lvl = 0;
  int num_args = 0;
  int result = -1;

  memset (tok, 0, sizeof (*tok) * ntok);

  old_input_line_pointer = input_line_pointer;
  input_line_pointer = str;

  while (*input_line_pointer)
    {
      SKIP_WHITESPACE ();
      char current_char = *input_line_pointer;

      if (current_char == '\0')
	{
	  break;
	}

      switch (current_char)
	{
	case ',':
	  input_line_pointer++;
	  if (saw_comma || !saw_arg)
	    goto cleanup;
	  saw_comma = true;
	  break;

	case '}':
	case ']':
	  ++input_line_pointer;
	  --brk_lvl;
	  if (!saw_arg || num_args == ntok)
	    goto cleanup;
	  tok->X_op = O_bracket;
	  ++tok;
	  ++num_args;
	  break;

	case '{':
	case '[':
	  input_line_pointer++;
	  if (brk_lvl || num_args == ntok)
	    goto cleanup;
	  ++brk_lvl;
	  tok->X_op = O_bracket;
	  ++tok;
	  ++num_args;
	  break;

	case ':':
	  input_line_pointer++;
	  if (!saw_arg || num_args == ntok)
	    goto cleanup;
	  tok->X_op = O_colon;
	  saw_arg = false;
	  ++tok;
	  ++num_args;
	  break;

	case '@':
	case '%':
	default:
	  if ((saw_arg && !saw_comma) || num_args == ntok)
	    goto cleanup;

	  if (current_char == '%')
	    {
	      ++input_line_pointer;
	    }

	  if (current_char == '@')
	    {
	      input_line_pointer++;
	      tok->X_op = O_symbol;
	    }
	  else
	    {
	      tok->X_op = O_absent;
	    }

	  tok->X_md = O_absent;
	  expression (tok);

	  if (*input_line_pointer == '@')
	    {
	      parse_reloc_symbol (tok);
	    }
	  else if (current_char != '@')
	    {
	      resolve_register (tok);
	    }

	  debug_exp (tok);

	  if (tok->X_op == O_illegal || tok->X_op == O_absent)
	    goto cleanup;

	  saw_comma = false;
	  saw_arg = true;
	  tok++;
	  num_args++;
	  break;
	}
    }

  if (saw_comma || brk_lvl)
    goto cleanup;

  result = num_args;

cleanup:
  if (result == -1)
    {
      if (brk_lvl)
	as_bad (_("Brackets in operand field incorrect"));
      else if (saw_comma)
	as_bad (_("extra comma"));
      else if (!saw_arg)
	as_bad (_("missing argument"));
      else
	as_bad (_("missing comma or colon"));
    }
  input_line_pointer = old_input_line_pointer;
  return result;
}

/* Parse the flags to a structure.  */

static int
tokenize_flags (const char *str,
		struct arc_flags flags[],
		int nflg)
{
  static const char VALID_FLAG_CHARS[] = "abcdefghijklmnopqrstuvwxyz0123456789";
  const char *p = str;
  int num_flags = 0;
  bool expect_flag = true;

  memset (flags, 0, sizeof (*flags) * nflg);

  while (*p && !is_end_of_stmt (*p) && !is_whitespace (*p))
    {
      if (*p == '.')
	{
	  p++;
	  if (expect_flag)
	    {
	      as_bad (_("extra dot"));
	      return -1;
	    }
	  expect_flag = true;
	}
      else
	{
	  if (!expect_flag)
	    {
	      as_bad (_("failed to parse flags"));
	      return -1;
	    }

	  if (num_flags >= nflg)
	    {
	      as_bad (_("failed to parse flags"));
	      return -1;
	    }

	  size_t flgnamelen = strspn (p, VALID_FLAG_CHARS);
	  if (flgnamelen == 0)
	    {
	      as_bad (_("unrecognized flag"));
	      return -1;
	    }

	  if (flgnamelen > MAX_FLAG_NAME_LENGTH)
	    {
	      as_bad (_("failed to parse flags"));
	      return -1;
	    }

	  memcpy (flags[num_flags].name, p, flgnamelen);

	  p += flgnamelen;
	  num_flags++;
	  expect_flag = false;
	}
    }

  return num_flags;
}

/* Apply the fixups in order.  */

static void
process_single_fixup (const struct arc_fixup *fixup, const struct arc_insn *insn,
                      fragS *fragP, int fix)
{
  /* Some fixups are only used internally, thus no howto.  */
  if (fixup->reloc == 0)
    {
      as_fatal (_("Unhandled reloc type"));
    }

  /* FIXME! the reloc size is wrong in the BFD file.
     When it is fixed please delete me.  */
  const int size = ((insn->len == 2) && !fixup->islong) ? 2 : 4;
  const int offset = fixup->islong ? insn->len : 0;
  const int is_internal_reloc = (int) fixup->reloc < 0;

  int pcrel;
  const char *reloc_name;

  if (is_internal_reloc)
    {
      /* FIXME! the reloc size is wrong in the BFD file.
         When it is fixed please enable me. */
      pcrel = fixup->pcrel;
      reloc_name = "Internal";
    }
  else
    {
      reloc_howto_type *reloc_howto =
        bfd_reloc_type_lookup (stdoutput, fixup->reloc);
      gas_assert (reloc_howto);

      /* FIXME! the reloc size is wrong in the BFD file.
         When it is fixed please enable me. */
      pcrel = reloc_howto->pc_relative;
      reloc_name = bfd_get_reloc_code_name (fixup->reloc);
    }

  pr_debug ("%s:%d: apply_fixups: new %s fixup (PCrel:%s) of size %d @ "
            "offset %d + %d\n",
            fragP->fr_file, fragP->fr_line, reloc_name,
            pcrel ? "Y" : "N", size, fix, offset);

  fix_new_exp (fragP, fix + offset, size, &fixup->exp, pcrel, fixup->reloc);

  /* Check for ZOLs, and update symbol info if any.  */
  if (LP_INSN (insn->insn))
    {
      gas_assert (fixup->exp.X_add_symbol);
      ARC_SET_FLAG (fixup->exp.X_add_symbol, ARC_FLAG_ZOL);
    }
}

static void
apply_fixups (struct arc_insn *insn, fragS *fragP, int fix)
{
  for (int i = 0; i < insn->nfixups; i++)
    {
      process_single_fixup (&insn->fixups[i], insn, fragP, fix);
    }
}

/* Actually output an instruction with its fixup.  */

static void
emit_insn0 (struct arc_insn *insn, char *where, bool relax)
{
  if (!insn)
    {
      return;
    }

  pr_debug ("Emit insn : 0x%llx\n", insn->insn);
  pr_debug ("\tLength  : %d\n", insn->len);
  pr_debug ("\tLong imm: 0x%lx\n", insn->limm);

  const size_t limm_size = 4;
  const size_t total_len = insn->len + (insn->has_limm ? limm_size : 0);
  char * const f = relax ? where : frag_more (total_len);

  md_number_to_chars_midend (f, insn->insn, insn->len);

  if (insn->has_limm)
    {
      md_number_to_chars_midend (f + insn->len, insn->limm, limm_size);
    }

  dwarf2_emit_insn (total_len);

  if (!relax)
    {
      apply_fixups (insn, frag_now, (f - frag_now->fr_literal));
    }
}

static void
emit_insn1 (struct arc_insn *insn)
{
  symbolS *s = make_expr_symbol (&insn->fixups[0].exp);
  frag_now->tc_frag_data.pcrel = insn->fixups[0].pcrel;
  relax_substateT subtype = frag_now->fr_subtype;

  if (frag_room () < FRAG_MAX_GROWTH)
    {
      struct arc_relax_type relax_info_copy = frag_now->tc_frag_data;

      frag_wane (frag_now);
      frag_grow (FRAG_MAX_GROWTH);

      frag_now->tc_frag_data = relax_info_copy;
    }

  frag_var (rs_machine_dependent, FRAG_MAX_GROWTH, 0, subtype, s, 0, 0);
}

static void
emit_insn (struct arc_insn *insn)
{
  if (insn == NULL)
    {
      return;
    }

  if (insn->relax)
    {
      emit_insn1 (insn);
    }
  else
    {
      emit_insn0 (insn, NULL, false);
    }
}

/* Check whether a symbol involves a register.  */

static bool
contains_register (symbolS *sym)
{
  if (!sym)
    {
      return false;
    }

  expressionS *ex = symbol_get_value_expression (sym);

  return (ex != NULL
	  && ex->X_op == O_register
	  && !contains_register (ex->X_add_symbol)
	  && !contains_register (ex->X_op_symbol));
}

/* Returns the register number within a symbol.  */

static int
get_register (symbolS *sym)
{
  if (sym != NULL && contains_register (sym))
    {
      expressionS *ex = symbol_get_value_expression (sym);
      if (ex != NULL)
        {
          return regno (ex->X_add_number);
        }
    }
  return -1;
}

/* Return true if a RELOC is generic.  A generic reloc is PC-rel of a
   simple ME relocation (e.g. RELOC_ARC_32_ME, BFD_RELOC_ARC_PC32.  */

static bool
generic_reloc_p (extended_bfd_reloc_code_real_type reloc)
{
  switch (reloc)
    {
    case 0:
    case BFD_RELOC_ARC_SDA_LDST:
    case BFD_RELOC_ARC_SDA_LDST1:
    case BFD_RELOC_ARC_SDA_LDST2:
    case BFD_RELOC_ARC_SDA16_LD:
    case BFD_RELOC_ARC_SDA16_LD1:
    case BFD_RELOC_ARC_SDA16_LD2:
    case BFD_RELOC_ARC_SDA16_ST2:
    case BFD_RELOC_ARC_SDA32_ME:
      return false;

    default:
      return true;
    }
}

/* Allocates a tok entry.  */

#include <string.h>

static int
allocate_tok (expressionS *tok, int ntok, int cidx)
{
  if (ntok >= MAX_INSN_ARGS - 1 || cidx < 0 || cidx > ntok)
    {
      return 0;
    }

  size_t count = ntok - cidx + 1;
  memmove (&tok[cidx + 1], &tok[cidx], count * sizeof (*tok));

  return 1;
}

/* Check if an particular ARC feature is enabled.  */

typedef struct
{
  bool (*is_feature_required) (insn_subclass_t);
  unsigned long feature_flag;
} cpu_feature_check_t;

static const cpu_feature_check_t FEATURE_CHECKS[] =
{
  { is_code_density_p, CD },
  { is_spfp_p,         SPX },
  { is_dpfp_p,         DPX },
  { is_fpuda_p,        DPA },
  { is_nps400_p,       NPS400 }
};

static bool
check_cpu_feature (insn_subclass_t sc)
{
  for (size_t i = 0; i < sizeof (FEATURE_CHECKS) / sizeof (FEATURE_CHECKS[0]); ++i)
    {
      if (FEATURE_CHECKS[i].is_feature_required (sc)
          && !(selected_cpu.features & FEATURE_CHECKS[i].feature_flag))
        {
          return false;
        }
    }

  return true;
}

/* Parse the flags described by FIRST_PFLAG and NFLGS against the flag
   operands in OPCODE.  Stores the matching OPCODES into the FIRST_PFLAG
   array and returns TRUE if the flag operands all match, otherwise,
   returns FALSE, in which case the FIRST_PFLAG array may have been
   modified.  */

static bool
match_and_update_flag (const struct arc_flag_operand *operand,
                       int nflgs,
                       struct arc_flags *parsed_flags,
                       int *matches_in_class,
                       int *remaining_flags)
{
  for (int i = 0; i < nflgs; ++i)
    {
      if (strcmp (operand->name, parsed_flags[i].name) == 0)
        {
          if (parsed_flags[i].flgp != NULL)
            {
              return false;
            }
          parsed_flags[i].flgp = operand;
          (*matches_in_class)++;
          (*remaining_flags)--;
          return true;
        }
    }
  return true;
}

static bool
parse_opcode_flags (const struct arc_opcode *opcode,
                    int nflgs,
                    struct arc_flags *first_pflag)
{
  int remaining_flags = nflgs;

  for (int i = 0; i < nflgs; i++)
    {
      first_pflag[i].flgp = NULL;
    }

  for (const unsigned char *flgidx = opcode->flags; *flgidx; ++flgidx)
    {
      const struct arc_flag_class *cl_flags = &arc_flag_classes[*flgidx];
      int cl_matches = 0;

      if ((cl_flags->flag_class & F_CLASS_IMPLICIT) != 0)
        {
          continue;
        }

      if (ext_condcode.arc_ext_condcode
          && (cl_flags->flag_class & F_CLASS_EXTEND) != 0)
        {
          for (const struct arc_flag_operand *pf = ext_condcode.arc_ext_condcode;
               pf->name; pf++)
            {
              if (!match_and_update_flag (pf, nflgs, first_pflag, &cl_matches,
                                          &remaining_flags))
                {
                  return false;
                }
            }
        }

      for (const unsigned *flgopridx = cl_flags->flags; *flgopridx; ++flgopridx)
        {
          const struct arc_flag_operand *flg_operand
            = &arc_flag_operands[*flgopridx];
          if (!match_and_update_flag (flg_operand, nflgs, first_pflag,
                                      &cl_matches, &remaining_flags))
            {
              return false;
            }
        }

      if ((((cl_flags->flag_class & F_CLASS_REQUIRED) != 0) && cl_matches == 0)
          || (((cl_flags->flag_class & F_CLASS_OPTIONAL) != 0) && cl_matches > 1))
        {
          return false;
        }
    }

  return remaining_flags == 0;
}


/* Search forward through all variants of an opcode looking for a
   syntax match.  */

static void
convert_aux_reg_symbol_if_needed (const struct arc_opcode *opcode,
                                  expressionS *current_tok)
{
  if (opcode->insn_class != AUXREG || current_tok->X_op != O_symbol)
    {
      return;
    }

  const char *p = S_GET_NAME (current_tok->X_add_symbol);
  char *tmpp = strdup (p);
  if (!tmpp)
    {
      return;
    }

  for (char *pp = tmpp; *pp; ++pp)
    {
      *pp = TOLOWER (*pp);
    }

  const struct arc_aux_reg *auxr = str_hash_find (arc_aux_hash, tmpp);
  free (tmpp);

  if (auxr)
    {
      current_tok->X_op = O_constant;
      current_tok->X_add_number = auxr->address;
      ARC_SET_FLAG (current_tok->X_add_symbol, ARC_FLAG_AUX);
    }
}

static bool
check_immediate_range_and_alignment (const struct arc_operand *operand,
				     offsetT val, const char **errmsg)
{
  if (operand->bits != 32 && !(operand->flags & ARC_OPERAND_NCHK))
    {
      offsetT min, max;
      if (operand->flags & ARC_OPERAND_SIGNED)
	{
	  max = (1LL << (operand->bits - 1)) - 1;
	  min = -(1LL << (operand->bits - 1));
	}
      else
	{
	  max = (1ULL << operand->bits) - 1;
	  min = 0;
	}
      if (val < min || val > max)
	{
	  *errmsg = _("immediate is out of bounds");
	  return false;
	}
    }

  if (((operand->flags & ARC_OPERAND_ALIGNED32) && (val & 0x03))
      || ((operand->flags & ARC_OPERAND_ALIGNED16) && (val & 0x01)))
    {
      *errmsg = (operand->flags & ARC_OPERAND_ALIGNED32)
		? _("immediate is not 32bit aligned")
		: _("immediate is not 16bit aligned");
      return false;
    }

  return true;
}

static bool
check_reloc_operand (const struct arc_operand *operand,
		     const expressionS *current_tok)
{
  if (operand->default_reloc == 0)
    {
      return false;
    }

  switch (current_tok->X_md)
    {
    case O_gotoff:
    case O_gotpc:
    case O_pcl:
    case O_tpoff:
    case O_dtpoff:
    case O_tlsgd:
    case O_tlsie:
      if (!(operand->flags & ARC_OPERAND_LIMM))
	{
	  return false;
	}
    case O_absent:
      if (!generic_reloc_p (operand->default_reloc))
	{
	  return false;
	}
      break;
    default:
      break;
    }
  return true;
}

static bool
match_immediate_operand (const struct arc_operand *operand,
			 expressionS *tok, int *pntok, int tokidx,
			 const expressionS *t,
			 const struct arc_opcode *opcode,
			 const char **errmsg)
{
  expressionS *current_tok = &tok[tokidx];
  switch (current_tok->X_op)
    {
    case O_illegal:
    case O_absent:
    case O_register:
      return false;

    case O_bracket:
      if (!(operand->flags & ARC_OPERAND_IGNORE))
	return false;
      if (!allocate_tok (tok, *pntok - 1, tokidx))
	return false;
      current_tok->X_op = O_absent;
      (*pntok)++;
      break;

    case O_symbol:
      convert_aux_reg_symbol_if_needed (opcode, current_tok);
      if (current_tok->X_op != O_constant)
	return check_reloc_operand (operand, current_tok);

    case O_constant:
      if (!check_immediate_range_and_alignment (operand,
						 current_tok->X_add_number,
						 errmsg))
	return false;
      if ((operand->flags & ARC_OPERAND_NCHK) && operand->insert)
	{
	  const char *tmpmsg = NULL;
	  (*operand->insert) (0, current_tok->X_add_number, &tmpmsg);
	  if (tmpmsg)
	    {
	      *errmsg = tmpmsg;
	      return false;
	    }
	}
      break;

    case O_subtract:
      if (current_tok->X_add_number == 0
	  && contains_register (current_tok->X_add_symbol)
	  && contains_register (current_tok->X_op_symbol))
	{
	  if (operand->insert)
	    {
	      const char *tmpmsg = NULL;
	      int regs = (get_register (current_tok->X_add_symbol) << 16)
			 | get_register (current_tok->X_op_symbol);
	      (*operand->insert) (0, regs, &tmpmsg);
	      if (tmpmsg)
		{
		  *errmsg = tmpmsg;
		  return false;
		}
	    }
	  else
	    {
	      return false;
	    }
	  break;
	}
    default:
      if (!check_reloc_operand (operand, current_tok))
	return false;
      break;
    }

  if (operand->flags & ARC_OPERAND_DUPLICATE)
    {
      if (t->X_op == O_illegal || t->X_op == O_absent
	  || t->X_op == O_register
	  || (t->X_add_number != current_tok->X_add_number))
	{
	  *errmsg = _("operand is not duplicate of the previous one");
	  return false;
	}
    }
  return true;
}

static bool
match_register_operand (const struct arc_operand *operand, expressionS *tok,
			int *pntok, int tokidx, const expressionS *t,
			const char **errmsg)
{
  expressionS *current_tok = &tok[tokidx];
  if ((current_tok->X_op != O_register || !is_ir_num (current_tok->X_add_number))
      && !(operand->flags & ARC_OPERAND_IGNORE))
    {
      return false;
    }

  if (operand->flags & ARC_OPERAND_DUPLICATE)
    {
      if (t->X_op != O_register || !is_ir_num (t->X_add_number)
	  || (regno (t->X_add_number) != regno (current_tok->X_add_number)))
	{
	  return false;
	}
    }

  if (operand->insert)
    {
      const char *tmpmsg = NULL;
      (*operand->insert) (0, regno (current_tok->X_add_number), &tmpmsg);
      if (tmpmsg)
	{
	  if (operand->flags & ARC_OPERAND_IGNORE)
	    {
	      if (!allocate_tok (tok, *pntok - 1, tokidx))
		return false;
	      current_tok->X_op = O_absent;
	      (*pntok)++;
	    }
	  else
	    {
	      *errmsg = tmpmsg;
	      return false;
	    }
	}
    }
  return true;
}

static bool
match_address_operand (const struct arc_operand *operand,
		       const expressionS *current_tok, const char **errmsg)
{
  if (current_tok->X_op != O_addrtype)
    {
      return false;
    }
  gas_assert (operand->insert != NULL);

  const char *tmpmsg = NULL;
  (*operand->insert) (0, current_tok->X_add_number, &tmpmsg);
  if (tmpmsg != NULL)
    {
      *errmsg = tmpmsg;
      return false;
    }
  return true;
}

static bool
match_one_operand (const struct arc_opcode *opcode,
		   const struct arc_operand *operand, expressionS *tok,
		   int *pntok, int tokidx, const expressionS **t,
		   const char **errmsg)
{
  bool matched = false;
  switch (operand->flags & ARC_OPERAND_TYPECHECK_MASK)
    {
    case ARC_OPERAND_ADDRTYPE:
      matched = match_address_operand (operand, &tok[tokidx], errmsg);
      break;

    case ARC_OPERAND_IR:
      matched = match_register_operand (operand, tok, pntok, tokidx, *t, errmsg);
      *t = &tok[tokidx];
      break;

    case ARC_OPERAND_BRAKET:
      matched = (tok[tokidx].X_op == O_bracket);
      break;

    case ARC_OPERAND_COLON:
      matched = (tok[tokidx].X_op == O_colon);
      break;

    case ARC_OPERAND_LIMM:
    case ARC_OPERAND_SIGNED:
    case ARC_OPERAND_UNSIGNED:
      matched = match_immediate_operand (operand, tok, pntok, tokidx, *t,
					  opcode, errmsg);
      *t = &tok[tokidx];
      break;

    default:
      abort ();
    }
  return matched;
}

static const struct arc_opcode *
find_opcode_match (const struct arc_opcode_hash_entry *entry,
		   expressionS *tok, int *pntok,
		   struct arc_flags *first_pflag, int nflgs,
		   int *pcpumatch, const char **errmsg)
{
  const struct arc_opcode *opcode;
  struct arc_opcode_hash_entry_iterator iter;
  expressionS bktok[MAX_INSN_ARGS];
  int bkntok;
  expressionS emptyE;
  int got_cpu_match = 0;
  int maxerridx = 0;

  arc_opcode_hash_entry_iterator_init (&iter);
  memset (&emptyE, 0, sizeof (emptyE));
  memcpy (bktok, tok, MAX_INSN_ARGS * sizeof (*tok));
  bkntok = *pntok;

  for (opcode = arc_opcode_hash_entry_iterator_next (entry, &iter);
       opcode != NULL;
       opcode = arc_opcode_hash_entry_iterator_next (entry, &iter))
    {
      int ntok = bkntok;
      bool match_failed = false;
      const char *current_errmsg = NULL;

      pr_debug ("%s:%d: find_opcode_match: trying opcode 0x%08llX ",
		frag_now->fr_file, frag_now->fr_line, opcode->opcode);

      if (!(opcode->cpu & selected_cpu.flags)
	  || !check_cpu_feature (opcode->subclass))
	{
	  pr_debug ("\n");
	  continue;
	}
      got_cpu_match = 1;
      pr_debug ("cpu ");

      memcpy (tok, bktok, MAX_INSN_ARGS * sizeof (*tok));
      const unsigned char *opidx;
      int tokidx = 0;
      const expressionS *t = &emptyE;

      for (opidx = opcode->operands; *opidx; ++opidx)
	{
	  const struct arc_operand *operand = &arc_operands[*opidx];
	  if (ARC_OPERAND_IS_FAKE (operand))
	    {
	      continue;
	    }
	  if (tokidx >= ntok)
	    {
	      match_failed = true;
	      break;
	    }
	  if (!match_one_operand (opcode, operand, tok, &ntok, tokidx, &t,
				  &current_errmsg))
	    {
	      match_failed = true;
	      break;
	    }
	  tokidx++;
	}

      if (!match_failed)
	{
	  pr_debug ("opr ");
	  if (parse_opcode_flags (opcode, nflgs, first_pflag))
	    {
	      pr_debug ("flg");
	      if (tokidx == ntok)
		{
		  *pntok = ntok;
		  pr_debug ("\n");
		  return opcode;
		}
	      current_errmsg = _("too many arguments");
	    }
	  else
	    {
	      current_errmsg = _("flag mismatch");
	    }
	}

      pr_debug ("\n");
      if (tokidx >= maxerridx && current_errmsg)
	{
	  maxerridx = tokidx;
	  *errmsg = current_errmsg;
	}
    }

  if (*pcpumatch)
    {
      *pcpumatch = got_cpu_match;
    }

  return NULL;
}

/* Swap operand tokens.  */

static void
swap_operand (expressionS *operand_array,
	      unsigned int source,
	      unsigned int destination)
{
  if (source == destination)
    {
      return;
    }

  expressionS temp = operand_array[source];
  operand_array[source] = operand_array[destination];
  operand_array[destination] = temp;
}

/* Check if *op matches *tok type.
   Returns FALSE if they don't match, TRUE if they match.  */

static bool
pseudo_operand_match (const expressionS *tok,
		      const struct arc_operand_operation *op)
{
  const struct arc_operand *operand_real = &arc_operands[op->operand_idx];
  const unsigned int flags = operand_real->flags;
  const unsigned int bits = operand_real->bits;

  switch (tok->X_op)
    {
    case O_constant:
      if (bits == 32 && (flags & ARC_OPERAND_LIMM))
	{
	  return true;
	}

      if (flags & ARC_OPERAND_IR)
	{
	  return false;
	}

      offsetT min, max;
      const offsetT val = tok->X_add_number + op->count;

      if (flags & ARC_OPERAND_SIGNED)
	{
	  const offsetT pwr_of_2 = (offsetT)1 << (bits - 1);
	  max = pwr_of_2 - 1;
	  min = -pwr_of_2;
	}
      else
	{
	  max = ((offsetT)1 << bits) - 1;
	  min = 0;
	}
      return val >= min && val <= max;

    case O_symbol:
      return (flags & ARC_OPERAND_LIMM)
	|| ((flags & ARC_OPERAND_SIGNED) && bits == 9);

    case O_register:
      return (flags & ARC_OPERAND_IR);

    case O_bracket:
      return (flags & ARC_OPERAND_BRAKET);

    default:
      return false;
    }
}

/* Find pseudo instruction in array.  */

static const struct arc_pseudo_insn *
find_pseudo_insn (const char *opname,
		  int ntok,
		  const expressionS *tok)
{
  for (unsigned int i = 0; i < arc_num_pseudo_insn; ++i)
    {
      const struct arc_pseudo_insn *candidate = &arc_pseudo_insns[i];

      if (strcmp (candidate->mnemonic_p, opname) != 0)
	    {
	      continue;
	    }

      bool operands_match = true;
      for (int j = 0; j < ntok; ++j)
	    {
	      if (!pseudo_operand_match (&tok[j], &candidate->operand[j]))
		    {
		      operands_match = false;
		      break;
		    }
	    }

      if (operands_match)
	    {
	      return candidate;
	    }
    }

  return NULL;
}

/* Assumes the expressionS *tok is of sufficient size.  */

static const struct arc_opcode_hash_entry *
find_special_case_pseudo (const char *opname,
			  int *ntok,
			  expressionS *tok,
			  int *nflgs,
			  struct arc_flags *pflags)
{
  const struct arc_pseudo_insn *pseudo_insn = find_pseudo_insn (opname, *ntok, tok);
  unsigned int i;

  if (pseudo_insn == NULL)
    return NULL;

  if (pseudo_insn->flag_r != NULL)
    *nflgs += tokenize_flags (pseudo_insn->flag_r, &pflags[*nflgs],
			      MAX_INSN_FLGS - *nflgs);

  for (i = 0; i < pseudo_insn->operand_cnt; ++i)
    {
      const struct arc_operand_operation *operand_pseudo = &pseudo_insn->operand[i];
      const struct arc_operand *operand_real = &arc_operands[operand_pseudo->operand_idx];

      if ((operand_real->flags & ARC_OPERAND_BRAKET)
	  && !operand_pseudo->needs_insert)
	continue;

      if (operand_pseudo->needs_insert)
	{
	  if (operand_real->flags & ARC_OPERAND_BRAKET)
	    {
	      tok[i].X_op = O_bracket;
	    }
	  else
	    {
	      char construct_operand[MAX_CONSTR_STR];
	      const char *format = (operand_real->flags & ARC_OPERAND_IR) ? "r%d" : "%d";
	      snprintf (construct_operand, MAX_CONSTR_STR, format,
			operand_pseudo->count);
	      tokenize_arguments (construct_operand, &tok[i], 1);
	    }
	  ++(*ntok);
	}
      else if (operand_pseudo->count != 0 && tok[i].X_op == O_constant)
	{
	  tok[i].X_add_number += operand_pseudo->count;
	}
    }

  for (i = 0; i < pseudo_insn->operand_cnt; ++i)
    {
      unsigned int swap_idx = pseudo_insn->operand[i].swap_operand_idx;
      if (swap_idx != i)
	{
	  swap_operand (tok, i, swap_idx);
	  break;
	}
    }

  return arc_find_opcode (pseudo_insn->mnemonic_r);
}

static const struct arc_opcode_hash_entry *
find_special_case_flag (const char *opname,
			int *nflgs,
			struct arc_flags *pflags)
{
  for (unsigned int i = 0; i < arc_num_flag_special; i++)
    {
      const struct arc_flag_special *special = &arc_flag_special_cases[i];
      const size_t op_len = strlen (special->name);

      if (strncmp (opname, special->name, op_len) != 0)
	{
	  continue;
	}

      const char *flag_candidate = opname + op_len;
      const unsigned int *flag_idx_ptr = special->flags;
      unsigned int flag_idx;

      while ((flag_idx = *flag_idx_ptr++) != 0)
	{
	  const char *flag_name = arc_flag_operands[flag_idx].name;
	  if (strcmp (flag_candidate, flag_name) == 0)
	    {
	      if (*nflgs >= MAX_INSN_FLGS)
		{
		  return NULL;
		}

	      const struct arc_opcode_hash_entry *entry = arc_find_opcode (special->name);
	      const size_t flag_len = strlen (flag_name);

	      memcpy (pflags[*nflgs].name, flag_name, flag_len);
	      pflags[*nflgs].name[flag_len] = '\0';
	      (*nflgs)++;

	      return entry;
	    }
	}
    }
  return NULL;
}

/* Used to find special case opcode.  */

static const struct arc_opcode_hash_entry *
find_special_case (const char *opname,
		   int *nflgs,
		   struct arc_flags *pflags,
		   expressionS *tok,
		   int *ntok)
{
  const struct arc_opcode_hash_entry *entry =
    find_special_case_pseudo (opname, ntok, tok, nflgs, pflags);

  if (entry)
    {
      return entry;
    }

  return find_special_case_flag (opname, nflgs, pflags);
}

/* Autodetect cpu attribute list.  */

static void
autodetect_attributes (const struct arc_opcode *opcode,
			 const expressionS *tok,
			 int ntok)
{
  static const struct mpy_type
  {
    unsigned feature;
    unsigned encoding;
  } mpy_list[] = {
    { MPY1E, 1 }, { MPY6E, 6 }, { MPY7E, 7 }, { MPY8E, 8 }, { MPY9E, 9 }
  };

  for (unsigned i = 0; i < ARRAY_SIZE (feature_list); i++)
    {
      if (opcode->subclass == feature_list[i].feature)
	{
	  selected_cpu.features |= feature_list[i].feature;
	}
    }

  for (unsigned i = 0; i < ARRAY_SIZE (mpy_list); i++)
    {
      if (opcode->subclass == mpy_list[i].feature)
	{
	  mpy_option = mpy_list[i].encoding;
	}
    }

  for (int i = 0; i < ntok; i++)
    {
      switch (tok[i].X_md)
	{
	case O_gotoff:
	case O_gotpc:
	case O_plt:
	  pic_option = 2;
	  break;
	case O_sda:
	  sda_option = 2;
	  break;
	case O_tlsgd:
	case O_tlsie:
	case O_tpoff9:
	case O_tpoff:
	case O_dtpoff9:
	case O_dtpoff:
	  tls_option = 1;
	  break;
	default:
	  break;
	}

      if (tok[i].X_op == O_register)
	{
	  long reg_num = tok[i].X_add_number;
	  if ((reg_num >= 4 && reg_num <= 9)
	      || (reg_num >= 16 && reg_num <= 25))
	    {
	      rf16_only = false;
	    }
	}
    }
}

/* Given an opcode name, pre-tockenized set of argumenst and the
   opcode flags, take it all the way through emission.  */

static void
assemble_tokens (const char *opname,
		 expressionS *tok,
		 int ntok,
		 struct arc_flags *pflags,
		 int nflgs)
{
  const struct arc_opcode_hash_entry *entry = arc_find_opcode (opname);
  if (!entry)
    entry = find_special_case (opname, &nflgs, pflags, tok, &ntok);

  if (!entry)
    {
      as_bad (_("unknown opcode '%s'"), opname);
      return;
    }

  pr_debug ("%s:%d: assemble_tokens: %s\n",
	    frag_now->fr_file, frag_now->fr_line, opname);

  int cpumatch = 1;
  const char *errmsg = NULL;
  const struct arc_opcode *opcode = find_opcode_match (entry, tok, &ntok, pflags,
						       nflgs, &cpumatch, &errmsg);

  if (opcode)
    {
      struct arc_insn insn;
      autodetect_attributes (opcode, tok, ntok);
      assemble_insn (opcode, tok, ntok, pflags, nflgs, &insn);
      emit_insn (&insn);
      return;
    }

  if (!cpumatch)
    as_bad (_("opcode '%s' not supported for target %s"), opname,
	    selected_cpu.name);
  else if (errmsg)
    as_bad (_("%s for instruction '%s'"), errmsg, opname);
  else
    as_bad (_("inappropriate arguments for opcode '%s'"), opname);
}

/* The public interface to the instruction assembler.  */

void
md_assemble (char *str)
{
  char *opname = NULL;
  expressionS tok[MAX_INSN_ARGS];
  struct arc_flags flags[MAX_INSN_FLGS];
  int ntok;
  int nflg;
  char *p;

  const char * const opcode_chars = "abcdefghijklmnopqrstuvwxyz_0123456789";
  size_t opnamelen = strspn (str, opcode_chars);
  opname = xmemdup0 (str, opnamelen);

  assembling_insn = true;

  p = str + opnamelen;

  if ((nflg = tokenize_flags (p, flags, MAX_INSN_FLGS)) == -1)
    {
      as_bad (_("syntax error"));
      goto cleanup;
    }

  for (; !is_end_of_stmt (*p); p++)
    {
      if (is_whitespace (*p))
        {
          break;
        }
    }

  if ((ntok = tokenize_arguments (p, tok, MAX_INSN_ARGS)) < 0)
    {
      as_bad (_("syntax error"));
      goto cleanup;
    }

  assemble_tokens (opname, tok, ntok, flags, nflg);

cleanup:
  assembling_insn = false;
  free (opname);
}

/* Callback to insert a register into the hash table.  */

static void
declare_register (const char *name, int number)
{
  symbolS *regS = symbol_create (name, reg_section,
                                 &zero_address_frag, number);

  if (regS == NULL)
  {
    as_fatal (_("failed to create symbol for register %s"), name);
    return;
  }

  if (str_hash_insert (arc_reg_hash, S_GET_NAME (regS), regS, 0) != NULL)
  {
    as_fatal (_("duplicate register name: %s"), name);
  }
}

/* Construct symbols for each of the general registers.  */

static void
declare_register_set (void)
{
  const int num_registers = 64;

  for (int i = 0; i < num_registers; ++i)
    {
      char name[32];

      snprintf (name, sizeof(name), "r%d", i);
      declare_register (name, i);

      if ((i % 2) == 0)
	{
	  snprintf (name, sizeof(name), "r%dr%d", i, i + 1);
	  declare_register (name, i);
	}
    }
}

/* Construct a symbol for an address type.  */

static void
declare_addrtype (const char *name, int number)
{
  symbolS *addrtypeS = symbol_create (name, undefined_section,
                                      &zero_address_frag, number);

  if (addrtypeS == NULL)
  {
    as_fatal (_("virtual memory exhausted"));
  }

  if (str_hash_insert (arc_addrtype_hash, name, addrtypeS, 0))
  {
    as_fatal (_("duplicate %s"), name);
  }
}

/* Port-specific assembler initialization.  This function is called
   once, at assembler startup time.  */

void
md_begin (void)
{
  const struct arc_opcode *opcode = arc_opcodes;

  if (mach_selection_mode == MACH_SELECTION_NONE)
    arc_select_cpu (TARGET_WITH_CPU, MACH_SELECTION_FROM_DEFAULT);

  /* The endianness can be chosen "at the factory".  */
  target_big_endian = byte_order == BIG_ENDIAN;

  if (!bfd_set_arch_mach (stdoutput, bfd_arch_arc, selected_cpu.mach))
    as_warn (_("could not set architecture and machine"));

  /* Set elf header flags.  */
  bfd_set_private_flags (stdoutput, selected_cpu.eflags);

  /* Set up a hash table for the instructions.  */
  arc_opcode_hash = htab_create_alloc (16, hash_string_tuple, eq_string_tuple,
				       arc_opcode_free, xcalloc, free);

  /* Initialize the hash table with the insns.  */
  do
    {
      const char *name = opcode->name;

      arc_insert_opcode (opcode);

      while (++opcode && opcode->name
	     && (opcode->name == name
		 || !strcmp (opcode->name, name)))
	continue;
    }while (opcode->name);

  /* Register declaration.  */
  arc_reg_hash = str_htab_create ();

  declare_register_set ();
  declare_register ("gp", 26);
  declare_register ("fp", 27);
  declare_register ("sp", 28);
  declare_register ("ilink", 29);
  declare_register ("ilink1", 29);
  declare_register ("ilink2", 30);
  declare_register ("blink", 31);

  /* XY memory registers.  */
  declare_register ("x0_u0", 32);
  declare_register ("x0_u1", 33);
  declare_register ("x1_u0", 34);
  declare_register ("x1_u1", 35);
  declare_register ("x2_u0", 36);
  declare_register ("x2_u1", 37);
  declare_register ("x3_u0", 38);
  declare_register ("x3_u1", 39);
  declare_register ("y0_u0", 40);
  declare_register ("y0_u1", 41);
  declare_register ("y1_u0", 42);
  declare_register ("y1_u1", 43);
  declare_register ("y2_u0", 44);
  declare_register ("y2_u1", 45);
  declare_register ("y3_u0", 46);
  declare_register ("y3_u1", 47);
  declare_register ("x0_nu", 48);
  declare_register ("x1_nu", 49);
  declare_register ("x2_nu", 50);
  declare_register ("x3_nu", 51);
  declare_register ("y0_nu", 52);
  declare_register ("y1_nu", 53);
  declare_register ("y2_nu", 54);
  declare_register ("y3_nu", 55);

  declare_register ("mlo", 57);
  declare_register ("mmid", 58);
  declare_register ("mhi", 59);

  declare_register ("acc1", 56);
  declare_register ("acc2", 57);

  declare_register ("lp_count", 60);
  declare_register ("pcl", 63);

  /* Initialize the last instructions.  */
  memset (&arc_last_insns[0], 0, sizeof (arc_last_insns));

  /* Aux register declaration.  */
  arc_aux_hash = str_htab_create ();

  const struct arc_aux_reg *auxr = &arc_aux_regs[0];
  unsigned int i;
  for (i = 0; i < arc_num_aux_regs; i++, auxr++)
    {
      if (!(auxr->cpu & selected_cpu.flags))
	continue;

      if ((auxr->subclass != NONE)
	  && !check_cpu_feature (auxr->subclass))
	continue;

      if (str_hash_insert (arc_aux_hash, auxr->name, auxr, 0) != 0)
	as_fatal (_("duplicate %s"), auxr->name);
    }

  /* Address type declaration.  */
  arc_addrtype_hash = str_htab_create ();

  declare_addrtype ("bd", ARC_NPS400_ADDRTYPE_BD);
  declare_addrtype ("jid", ARC_NPS400_ADDRTYPE_JID);
  declare_addrtype ("lbd", ARC_NPS400_ADDRTYPE_LBD);
  declare_addrtype ("mbd", ARC_NPS400_ADDRTYPE_MBD);
  declare_addrtype ("sd", ARC_NPS400_ADDRTYPE_SD);
  declare_addrtype ("sm", ARC_NPS400_ADDRTYPE_SM);
  declare_addrtype ("xa", ARC_NPS400_ADDRTYPE_XA);
  declare_addrtype ("xd", ARC_NPS400_ADDRTYPE_XD);
  declare_addrtype ("cd", ARC_NPS400_ADDRTYPE_CD);
  declare_addrtype ("cbd", ARC_NPS400_ADDRTYPE_CBD);
  declare_addrtype ("cjid", ARC_NPS400_ADDRTYPE_CJID);
  declare_addrtype ("clbd", ARC_NPS400_ADDRTYPE_CLBD);
  declare_addrtype ("cm", ARC_NPS400_ADDRTYPE_CM);
  declare_addrtype ("csd", ARC_NPS400_ADDRTYPE_CSD);
  declare_addrtype ("cxa", ARC_NPS400_ADDRTYPE_CXA);
  declare_addrtype ("cxd", ARC_NPS400_ADDRTYPE_CXD);
}

void
arc_md_end (void)
{
  htab_t *const tables_to_clean[] = {
    &arc_opcode_hash,
    &arc_reg_hash,
    &arc_aux_hash,
    &arc_addrtype_hash
  };
  
  for (size_t i = 0; i < sizeof (tables_to_clean) / sizeof (tables_to_clean[0]); ++i)
    {
      if (*tables_to_clean[i])
        {
          htab_delete (*tables_to_clean[i]);
          *tables_to_clean[i] = NULL;
        }
    }
}

/* Write a value out to the object file, using the appropriate
   endianness.  */

void
md_number_to_chars (char *buf,
                    valueT val,
                    int n)
{
    if (buf == NULL || n <= 0)
    {
        return;
    }

    if (target_big_endian)
    {
        number_to_chars_bigendian (buf, val, n);
    }
    else
    {
        number_to_chars_littleendian (buf, val, n);
    }
}

/* Round up a section size to the appropriate boundary.  */

valueT
md_section_align (segT segment, valueT size)
{
  const int align = bfd_section_alignment (segment);

  if (align < 0 || (unsigned int) align >= (sizeof (valueT) * 8))
    {
      return size;
    }

  const valueT boundary = (valueT) 1 << align;
  const valueT mask = ~ (boundary - 1);

  return (size + boundary - 1) & mask;
}

/* The location from which a PC relative jump should be calculated,
   given a PC relative reloc.  */

long
md_pcrel_from_section (fixS *fixP, segT sec)
{
  offsetT base = fixP->fx_where + fixP->fx_frag->fr_address;

  pr_debug ("pcrel_from_section, fx_offset = %d\n", (int) fixP->fx_offset);

  if (fixP->fx_addsy != NULL
      && (!S_IS_DEFINED (fixP->fx_addsy)
	  || S_GET_SEGMENT (fixP->fx_addsy) != sec))
    {
      pr_debug ("Unknown pcrel symbol: %s\n", S_GET_NAME (fixP->fx_addsy));
      return 0;
    }

  switch (fixP->fx_r_type)
    {
    case BFD_RELOC_ARC_PC32:
      base -= 4;
      /* Fall through for alignment. */
    case BFD_RELOC_ARC_PLT32:
    case BFD_RELOC_ARC_S25H_PCREL_PLT:
    case BFD_RELOC_ARC_S21H_PCREL_PLT:
    case BFD_RELOC_ARC_S25W_PCREL_PLT:
    case BFD_RELOC_ARC_S21W_PCREL_PLT:
    case BFD_RELOC_ARC_S21H_PCREL:
    case BFD_RELOC_ARC_S25H_PCREL:
    case BFD_RELOC_ARC_S13_PCREL:
    case BFD_RELOC_ARC_S21W_PCREL:
    case BFD_RELOC_ARC_S25W_PCREL:
      base &= ~3;
      break;

    default:
      if ((int) fixP->fx_r_type < 0)
	{
	  /* "Internal" relocations are aligned to a 32-bit boundary. */
	  base &= ~3;
	}
      else
	{
	  as_bad_where (fixP->fx_file, fixP->fx_line,
			_("unhandled reloc %s in md_pcrel_from_section"),
			bfd_get_reloc_code_name (fixP->fx_r_type));
	}
      break;
    }

  pr_debug ("pcrel from %" PRIx64 " + %lx = %" PRIx64 ", "
	    "symbol: %s (%" PRIx64 ")\n",
	    (uint64_t) fixP->fx_frag->fr_address, fixP->fx_where, (uint64_t) base,
	    fixP->fx_addsy ? S_GET_NAME (fixP->fx_addsy) : "(null)",
	    fixP->fx_addsy ? (uint64_t) S_GET_VALUE (fixP->fx_addsy) : 0);

  return base;
}

/* Given a BFD relocation find the corresponding operand.  */

static const struct arc_operand *
find_operand_for_reloc (extended_bfd_reloc_code_real_type reloc)
{
  for (unsigned int i = 0; i < arc_num_operands; i++)
    {
      if (arc_operands[i].default_reloc == reloc)
        {
          return &arc_operands[i];
        }
    }

  return NULL;
}

/* Insert an operand value into an instruction.  */

static unsigned long long
insert_operand (unsigned long long insn,
		const struct arc_operand *operand,
		long long val,
		const char *file,
		unsigned line)
{
  if (operand->bits != 32
      && !(operand->flags & ARC_OPERAND_NCHK)
      && !(operand->flags & ARC_OPERAND_FAKE))
    {
      long long min = 0, max = 0;
      if (operand->flags & ARC_OPERAND_SIGNED)
	{
	  max = (1ULL << (operand->bits - 1)) - 1;
	  min = -(1ULL << (operand->bits - 1));
	}
      else
	{
	  max = (1ULL << operand->bits) - 1;
	}

      if (val < min || val > max)
	{
	  as_bad_value_out_of_range (_("operand"), val, min, max, file, line);
	}

      pr_debug ("insert field: %lld <= %lld <= %lld in 0x%08llx\n",
		min, val, max, insn);
    }

  if ((operand->flags & ARC_OPERAND_ALIGNED32) && (val & 0x03))
    {
      as_bad_where (file, line,
		    _("Unaligned operand. Needs to be 32bit aligned"));
    }
  else if ((operand->flags & ARC_OPERAND_ALIGNED16) && (val & 0x01))
    {
      as_bad_where (file, line,
		    _("Unaligned operand. Needs to be 16bit aligned"));
    }

  if (operand->insert)
    {
      const char *errmsg = NULL;
      insn = (*operand->insert) (insn, val, &errmsg);
      if (errmsg)
	{
	  as_warn_where (file, line, "%s", errmsg);
	}
    }
  else
    {
      long long value_to_insert = val;
      if (operand->flags & ARC_OPERAND_TRUNCATE)
	{
	  if (operand->flags & ARC_OPERAND_ALIGNED32)
	    {
	      value_to_insert >>= 2;
	    }
	  else if (operand->flags & ARC_OPERAND_ALIGNED16)
	    {
	      value_to_insert >>= 1;
	    }
	}

      unsigned long long mask = (operand->bits >= 64)
	? ~0ULL : (1ULL << operand->bits) - 1;
      insn |= (unsigned long long) (value_to_insert & mask) << operand->shift;
    }
  return insn;
}

/* Apply a fixup to the object code.  At this point all symbol values
   should be fully resolved, and we attempt to completely resolve the
   reloc.  If we can not do that, we determine the correct reloc code
   and put it back in the fixup.  To indicate that a fixup has been
   eliminated, set fixP->fx_done.  */

static bool
is_sub_symbol_tls_exempt (bfd_reloc_code_real_type r_type)
{
  return r_type == BFD_RELOC_ARC_TLS_DTPOFF
    || r_type == BFD_RELOC_ARC_TLS_DTPOFF_S9
    || r_type == BFD_RELOC_ARC_TLS_GD_LD;
}

static void
handle_pcrel_fixup (fixS *fixP, valueT *value, segT seg)
{
  if (!fixP->fx_pcrel)
    return;

  if (fixP->fx_addsy
      && ((S_IS_DEFINED (fixP->fx_addsy)
	   && S_GET_SEGMENT (fixP->fx_addsy) != seg)
	  || S_IS_WEAK (fixP->fx_addsy)))
    *value += md_pcrel_from_section (fixP, seg);

  switch (fixP->fx_r_type)
    {
    case BFD_RELOC_ARC_32_ME:
      fixP->fx_offset += fixP->fx_frag->fr_address;
      /* Fall through. */
    case BFD_RELOC_32:
      fixP->fx_r_type = BFD_RELOC_ARC_PC32;
      /* Fall through. */
    case BFD_RELOC_ARC_PC32:
      break;
    default:
      if ((int) fixP->fx_r_type < 0)
	as_bad_where (fixP->fx_file, fixP->fx_line,
		      _("PC relative relocation not allowed for (internal) type %d"),
		      fixP->fx_r_type);
      break;
    }
}

static void
handle_tls_relocations (fixS *fixP)
{
  switch (fixP->fx_r_type)
    {
    case BFD_RELOC_ARC_TLS_DTPOFF:
    case BFD_RELOC_ARC_TLS_LE_32:
      if (fixP->fx_done)
	break;
      /* Fall through. */
    case BFD_RELOC_ARC_TLS_GD_GOT:
    case BFD_RELOC_ARC_TLS_IE_GOT:
      S_SET_THREAD_LOCAL (fixP->fx_addsy);
      break;

    case BFD_RELOC_ARC_TLS_GD_LD:
      gas_assert (!fixP->fx_offset);
      if (fixP->fx_subsy)
	{
	  fixP->fx_offset = (S_GET_VALUE (fixP->fx_subsy)
			     - fixP->fx_frag->fr_address - fixP->fx_where);
	  fixP->fx_subsy = NULL;
	}
      /* Fall through. */
    case BFD_RELOC_ARC_TLS_GD_CALL:
      S_SET_THREAD_LOCAL (fixP->fx_addsy);
      break;

    case BFD_RELOC_ARC_TLS_LE_S9:
    case BFD_RELOC_ARC_TLS_DTPOFF_S9:
      as_bad (_("TLS_*_S9 relocs are not supported yet"));
      break;

    default:
      break;
    }
}

static extended_bfd_reloc_code_real_type
map_plt_reloc (extended_bfd_reloc_code_real_type reloc)
{
  switch (reloc)
    {
    case BFD_RELOC_ARC_S25H_PCREL_PLT:
      return BFD_RELOC_ARC_S25W_PCREL;
    case BFD_RELOC_ARC_S21H_PCREL_PLT:
      return BFD_RELOC_ARC_S21H_PCREL;
    case BFD_RELOC_ARC_S25W_PCREL_PLT:
      return BFD_RELOC_ARC_S25W_PCREL;
    case BFD_RELOC_ARC_S21W_PCREL_PLT:
      return BFD_RELOC_ARC_S21W_PCREL;
    default:
      return reloc;
    }
}

static void
encode_and_write_instruction (char *fixpos, const fixS *fixP,
			      const struct arc_operand *operand, valueT value)
{
  unsigned int insn = 0;

  switch (fixP->fx_size)
    {
    case 4:
      if (target_big_endian)
	insn = bfd_getb32 (fixpos);
      else
	insn = bfd_getl16 (fixpos) << 16 | bfd_getl16 (fixpos + 2);
      break;
    case 2:
      if (target_big_endian)
	insn = bfd_getb16 (fixpos);
      else
	insn = bfd_getl16 (fixpos);
      break;
    default:
      as_bad_where (fixP->fx_file, fixP->fx_line, _("unknown fixup size"));
      return;
    }

  insn = insert_operand (insn, operand, (offsetT) value,
			 fixP->fx_file, fixP->fx_line);

  md_number_to_chars_midend (fixpos, insn, fixP->fx_size);
}

void
md_apply_fix (fixS *fixP,
	      valueT *valP,
	      segT seg)
{
  char * const fixpos = fixP->fx_frag->fr_literal + fixP->fx_where;
  valueT value = *valP;
  symbolS *fx_addsy = fixP->fx_addsy;
  symbolS *fx_subsy = fixP->fx_subsy;
  offsetT fx_offset = 0;
  const struct arc_operand *operand = NULL;
  extended_bfd_reloc_code_real_type reloc;

  pr_debug ("%s:%u: apply_fix: r_type=%d (%s) value=0x%lX offset=0x%lX\n",
	    fixP->fx_file, fixP->fx_line, fixP->fx_r_type,
	    ((int) fixP->fx_r_type < 0) ? "Internal"
	    : bfd_get_reloc_code_name (fixP->fx_r_type), value,
	    fixP->fx_offset);

  if (fx_subsy && !is_sub_symbol_tls_exempt (fixP->fx_r_type))
    {
      resolve_symbol_value (fx_subsy);
      if (S_GET_SEGMENT (fx_subsy) == absolute_section)
	{
	  fx_offset -= S_GET_VALUE (fx_subsy);
	  fx_subsy = NULL;
	}
      else
	{
	  as_bad_subtract (fixP);
	  return;
	}
    }

  if (fx_addsy && !S_IS_WEAK (fx_addsy))
    {
      segT add_symbol_segment = S_GET_SEGMENT (fx_addsy);
      if (add_symbol_segment == seg && fixP->fx_pcrel)
	{
	  value += S_GET_VALUE (fx_addsy);
	  value -= md_pcrel_from_section (fixP, seg);
	  fx_addsy = NULL;
	  fixP->fx_pcrel = false;
	}
      else if (add_symbol_segment == absolute_section)
	{
	  value = fixP->fx_offset;
	  fx_offset += S_GET_VALUE (fixP->fx_addsy);
	  fx_addsy = NULL;
	  fixP->fx_pcrel = false;
	}
    }

  fixP->fx_done = (fx_addsy == NULL);

  handle_pcrel_fixup (fixP, &value, seg);
  handle_tls_relocations (fixP);

  if (!fixP->fx_done)
    return;

  value += fx_offset;

  if (value & 0x80000000)
    value |= ((valueT) -1) << 31;

  reloc = fixP->fx_r_type;
  switch (reloc)
    {
    case BFD_RELOC_8:
    case BFD_RELOC_16:
    case BFD_RELOC_24:
    case BFD_RELOC_32:
    case BFD_RELOC_64:
    case BFD_RELOC_ARC_32_PCREL:
      md_number_to_chars (fixpos, value, fixP->fx_size);
      return;

    case BFD_RELOC_ARC_GOTPC32:
      as_bad (_("Unsupported operation on reloc"));
      return;

    case BFD_RELOC_ARC_TLS_DTPOFF:
    case BFD_RELOC_ARC_TLS_LE_32:
      gas_assert (!fixP->fx_addsy);
      gas_assert (!fixP->fx_subsy);
      /* Fall through. */
    case BFD_RELOC_ARC_GOTOFF:
    case BFD_RELOC_ARC_32_ME:
    case BFD_RELOC_ARC_PC32:
    case BFD_RELOC_ARC_PLT32:
      md_number_to_chars_midend (fixpos, value, fixP->fx_size);
      return;

    case BFD_RELOC_ARC_S25H_PCREL_PLT:
    case BFD_RELOC_ARC_S21H_PCREL_PLT:
    case BFD_RELOC_ARC_S25W_PCREL_PLT:
    case BFD_RELOC_ARC_S21W_PCREL_PLT:
    case BFD_RELOC_ARC_S25W_PCREL:
    case BFD_RELOC_ARC_S21W_PCREL:
    case BFD_RELOC_ARC_S21H_PCREL:
    case BFD_RELOC_ARC_S25H_PCREL:
    case BFD_RELOC_ARC_S13_PCREL:
      reloc = map_plt_reloc (reloc);
      operand = find_operand_for_reloc (reloc);
      gas_assert (operand);
      break;

    default:
      if ((int) reloc >= 0)
	{
	  as_fatal (_("unhandled relocation type %s"),
		    bfd_get_reloc_code_name (reloc));
	  return;
	}

      if (fixP->fx_addsy != NULL
	  && S_GET_SEGMENT (fixP->fx_addsy) != absolute_section)
	{
	  as_bad_where (fixP->fx_file, fixP->fx_line,
			_("non-absolute expression in constant field"));
	  return;
	}

      gas_assert (-(int) reloc < (int) arc_num_operands);
      operand = &arc_operands[-(int) reloc];
      break;
    }

  if (operand)
    encode_and_write_instruction (fixpos, fixP, operand, value);
}

/* Prepare machine-dependent frags for relaxation.

   Called just before relaxation starts.  Any symbol that is now undefined
   will not become defined.

   Return the correct fr_subtype in the frag.

   Return the initial "guess for fr_var" to caller.  The guess for fr_var
   is *actually* the growth beyond fr_fix.  Whatever we do to grow fr_fix
   or fr_var contributes to our returned value.

   Although it may not be explicit in the frag, pretend
   fr_var starts with a value.  */

static int
should_use_max_relaxation (const fragS *fragP, segT segment)
{
  const symbolS *symbol = fragP->fr_symbol;

  if (S_GET_SEGMENT (symbol) != segment
      && S_GET_SEGMENT (symbol) != absolute_section)
    {
      return 1;
    }

  if (symbol_constant_p (symbol) && !fragP->tc_frag_data.pcrel)
    {
      return 1;
    }

  if (symbol_equated_p (symbol))
    {
      return 1;
    }

  if (S_IS_WEAK (symbol))
    {
      return 1;
    }

  return 0;
}

static void
find_max_relaxation_state (fragS *fragP)
{
  while (md_relax_table[fragP->fr_subtype].rlx_more != ARC_RLX_NONE)
    {
      fragP->fr_subtype++;
    }
}

int
md_estimate_size_before_relax (fragS *fragP,
			       segT segment)
{
  if (should_use_max_relaxation (fragP, segment))
    {
      find_max_relaxation_state (fragP);
    }

  int growth = md_relax_table[fragP->fr_subtype].rlx_length;
  fragP->fr_var = growth;

  pr_debug ("%s:%d: md_estimate_size_before_relax: %d\n",
	    fragP->fr_file, fragP->fr_line, growth);

  return growth;
}

/* Translate internal representation of relocation info to BFD target
   format.  */

arelent *
tc_gen_reloc (asection *section ATTRIBUTE_UNUSED,
	      fixS *fixP)
{
  arelent *reloc;
  bfd_reloc_code_real_type code;

  reloc = notes_alloc (sizeof (*reloc));
  if (reloc == NULL)
    {
      return NULL;
    }

  reloc->sym_ptr_ptr = notes_alloc (sizeof (*reloc->sym_ptr_ptr));
  if (reloc->sym_ptr_ptr == NULL)
    {
      return NULL;
    }

  *reloc->sym_ptr_ptr = symbol_get_bfdsym (fixP->fx_addsy);
  reloc->address = fixP->fx_frag->fr_address + fixP->fx_where;

  /* Make sure none of our internal relocations make it this far.
     They'd better have been fully resolved by this point.  */
  gas_assert ((int) fixP->fx_r_type > 0);

  code = fixP->fx_r_type;

  /* if we have something like add gp, pcl,
     _GLOBAL_OFFSET_TABLE_@gotpc.  */
  if (code == BFD_RELOC_ARC_GOTPC32
      && GOT_symbol
      && fixP->fx_addsy == GOT_symbol)
    {
      code = BFD_RELOC_ARC_GOTPC;
    }

  reloc->howto = bfd_reloc_type_lookup (stdoutput, code);
  if (reloc->howto == NULL)
    {
      as_bad_where (fixP->fx_file, fixP->fx_line,
		    _("cannot represent `%s' relocation in object file"),
		    bfd_get_reloc_code_name (code));
      return NULL;
    }

  if ((fixP->fx_pcrel != 0) != (reloc->howto->pc_relative != 0))
    {
      as_fatal (_("internal error? cannot generate `%s' relocation"),
	      bfd_get_reloc_code_name (code));
    }

  reloc->addend = fixP->fx_offset;

  return reloc;
}

/* Perform post-processing of machine-dependent frags after relaxation.
   Called after relaxation is finished.
   In:	Address of frag.
   fr_type == rs_machine_dependent.
   fr_subtype is what the address relaxed to.

   Out: Any fixS:s and constants are set up.  */

void
md_convert_frag (bfd *abfd ATTRIBUTE_UNUSED,
		 segT segment ATTRIBUTE_UNUSED,
		 fragS *fragP)
{
  gas_assert (fragP != NULL);

  pr_debug ("%s:%d: md_convert_frag, subtype: %d, fix: %d, "
	    "var: %" PRId64 "\n",
	    fragP->fr_file, fragP->fr_line,
	    fragP->fr_subtype, fragP->fr_fix, (int64_t) fragP->fr_var);

  if ((unsigned int) fragP->fr_subtype >= (unsigned int) arc_num_relax_opcodes)
    {
      as_fatal (_("no relaxation found for this instruction."));
    }

  const relax_typeS * const table_entry =
    TC_GENERIC_RELAX_TABLE + fragP->fr_subtype;
  const struct arc_opcode * const opcode =
    &arc_relax_opcodes[fragP->fr_subtype];
  const struct arc_relax_type * const relax_arg = &fragP->tc_frag_data;
  char * const dest = fragP->fr_literal + fragP->fr_fix;

  struct arc_insn insn;
  assemble_insn (opcode, relax_arg->tok, relax_arg->ntok, relax_arg->pflags,
		 relax_arg->nflg, &insn);

  apply_fixups (&insn, fragP, fragP->fr_fix);

  gas_assert (table_entry->rlx_length == (insn.len + (insn.has_limm ? 4 : 0)));
  emit_insn0 (&insn, dest, true);

  fragP->fr_fix += table_entry->rlx_length;
  fragP->fr_var = 0;
}

/* We have no need to default values of symbols.  We could catch
   register names here, but that is handled by inserting them all in
   the symbol table to begin with.  */

symbolS *
md_undefined_symbol (char *name)
{
  if (strcmp(name, GLOBAL_OFFSET_TABLE_NAME) != 0)
    {
      return NULL;
    }

  if (!GOT_symbol)
    {
      if (symbol_find (name))
        {
          as_bad ("GOT already in symbol table");
        }
      GOT_symbol = symbol_new (GLOBAL_OFFSET_TABLE_NAME, undefined_section,
                               &zero_address_frag, 0);
    }

  return GOT_symbol;
}

/* Turn a string in input_line_pointer into a floating point constant
   of type type, and store the appropriate bytes in *litP.  The number
   of LITTLENUMS emitted is stored in *sizeP.  An error message is
   returned, or NULL on OK.  */

const char *md_atof(int type, const char *litP, int *sizeP)
{
    return ieee_md_atof(type, litP, sizeP, target_big_endian);
}

/* Called for any expression that can not be recognized.  When the
   function is called, `input_line_pointer' will point to the start of
   the expression.  We use it when we have complex operations like
   @label1 - @label2.  */

void
md_operand (expressionS *expressionP)
{
  if (expressionP == NULL || input_line_pointer == NULL)
    {
      return;
    }

  if (*input_line_pointer == '@')
    {
      input_line_pointer++;
      expressionP->X_op = O_symbol;
      expressionP->X_md = O_absent;
      expression (expressionP);
    }
}

/* This function is called from the function 'expression', it attempts
   to parse special names (in our case register names).  It fills in
   the expression with the identified register.  It returns TRUE if
   it is a register and FALSE otherwise.  */

bool
arc_parse_name (const char *name,
		struct expressionS *e)
{
  if (!assembling_insn)
    return false;

  if (e->X_op == O_symbol
      && e->X_md == O_absent)
    return false;

  struct symbol *sym = str_hash_find (arc_reg_hash, name);
  int op_type = O_register;

  if (!sym)
    {
      sym = str_hash_find (arc_addrtype_hash, name);
      op_type = O_addrtype;
    }

  if (sym)
    {
      e->X_op = op_type;
      e->X_add_number = S_GET_VALUE (sym);
      return true;
    }

  return false;
}

/* md_parse_option
   Invocation line includes a switch not recognized by the base assembler.
   See if it's a processor-specific option.

   New options (supported) are:

   -mcpu=<cpu name>		 Assemble for selected processor
   -EB/-mbig-endian		 Big-endian
   -EL/-mlittle-endian		 Little-endian
   -mrelax                       Enable relaxation

   The following CPU names are recognized:
   arc600, arc700, arcem, archs, nps400.  */

static void
set_and_check_feature (unsigned long feature)
{
  selected_cpu.features |= feature;
  cl_features |= feature;
  arc_check_feature ();
}

int
md_parse_option (int c, const char *arg)
{
  switch (c)
    {
    case OPTION_ARC600:
    case OPTION_ARC601:
      arc_select_cpu ("arc600", MACH_SELECTION_FROM_COMMAND_LINE);
      break;

    case OPTION_ARC700:
      arc_select_cpu ("arc700", MACH_SELECTION_FROM_COMMAND_LINE);
      break;

    case OPTION_ARCEM:
      arc_select_cpu ("arcem", MACH_SELECTION_FROM_COMMAND_LINE);
      break;

    case OPTION_ARCHS:
      arc_select_cpu ("archs", MACH_SELECTION_FROM_COMMAND_LINE);
      break;

    case OPTION_MCPU:
      arc_select_cpu (arg, MACH_SELECTION_FROM_COMMAND_LINE);
      break;

    case OPTION_EB:
      arc_target_format = "elf32-bigarc";
      byte_order = BIG_ENDIAN;
      break;

    case OPTION_EL:
      arc_target_format = "elf32-littlearc";
      byte_order = LITTLE_ENDIAN;
      break;

    case OPTION_CD:
      set_and_check_feature (CD);
      break;

    case OPTION_NPS400:
      set_and_check_feature (NPS400);
      break;

    case OPTION_SPFP:
      set_and_check_feature (SPX);
      break;

    case OPTION_DPFP:
      set_and_check_feature (DPX);
      break;

    case OPTION_FPUDA:
      set_and_check_feature (DPA);
      break;

    case OPTION_RELAX:
      relaxation_state = 1;
      break;

    case OPTION_USER_MODE:
    case OPTION_LD_EXT_MASK:
    case OPTION_SWAP:
    case OPTION_NORM:
    case OPTION_BARREL_SHIFT:
    case OPTION_MIN_MAX:
    case OPTION_NO_MPY:
    case OPTION_EA:
    case OPTION_MUL64:
    case OPTION_SIMD:
    case OPTION_XMAC_D16:
    case OPTION_XMAC_24:
    case OPTION_DSP_PACKA:
    case OPTION_CRC:
    case OPTION_DVBF:
    case OPTION_TELEPHONY:
    case OPTION_XYMEMORY:
    case OPTION_LOCK:
    case OPTION_SWAPE:
    case OPTION_RTSC:
      break;

    default:
      return 0;
    }

  return 1;
}

/* Display the list of cpu names for use in the help text.  */

static void
arc_show_cpu_list (FILE *stream)
{
  static const char * const INDENT = "                          ";
  static const int TARGET_WIDTH = 80;
  const size_t indent_len = strlen (INDENT);

  if (fprintf (stream, "%s", INDENT) < 0)
    {
      return;
    }
  size_t current_offset = indent_len;

  for (size_t i = 0; cpu_types[i].name != NULL; ++i)
    {
      const char * const name = cpu_types[i].name;
      const size_t name_len = strlen (name);
      const bool is_last = (cpu_types[i + 1].name == NULL);
      const size_t separator_len_for_calc = is_last ? 0 : 2;

      if (current_offset + name_len + separator_len_for_calc > TARGET_WIDTH)
        {
          if (fprintf (stream, "\n%s", INDENT) < 0)
            {
              return;
            }
          current_offset = indent_len;
        }

      const char * const separator = is_last ? "\n" : ", ";
      if (fprintf (stream, "%s%s", name, separator) < 0)
        {
          return;
        }
      current_offset += name_len + separator_len_for_calc;
    }
}

void
md_show_usage (FILE *stream)
{
  fprintf (stream, _("ARC-specific assembler options:\n"));

  fprintf (stream, "  -mcpu=<cpu name>\t  (default: %s), assemble for"
           " CPU <cpu name>, one of:\n", TARGET_WITH_CPU);
  arc_show_cpu_list (stream);

  fprintf (stream, "\n"
           "  -mA6/-mARC600/-mARC601  same as -mcpu=arc600\n"
           "  -mA7/-mARC700\t\t  same as -mcpu=arc700\n"
           "  -mEM\t\t\t  same as -mcpu=arcem\n"
           "  -mHS\t\t\t  same as -mcpu=archs\n"
           "  -mnps400\t\t  enable NPS-400 extended instructions\n"
           "  -mspfp\t\t  enable single-precision floating point"
           " instructions\n"
           "  -mdpfp\t\t  enable double-precision floating point"
           " instructions\n"
           "  -mfpuda\t\t  enable double-precision assist floating "
           "point\n\t\t\t  instructions for ARC EM\n"
           "  -mcode-density\t  enable code density option for ARC EM\n");

  fprintf (stream, _("  -EB                     assemble code for a big-endian cpu\n"
                     "  -EL                     assemble code for a little-endian cpu\n"
                     "  -mrelax                 enable relaxation\n"));

  fprintf (stream, _("The following ARC-specific assembler options are "
                     "deprecated and are accepted\nfor compatibility only:\n"));

  fprintf (stream, _("  -mEA\n"
                     "  -mbarrel-shifter\n"
                     "  -mbarrel_shifter\n"
                     "  -mcrc\n"
                     "  -mdsp-packa\n"
                     "  -mdsp_packa\n"
                     "  -mdvbf\n"
                     "  -mld-extension-reg-mask\n"
                     "  -mlock\n"
                     "  -mmac-24\n"
                     "  -mmac-d16\n"
                     "  -mmac_24\n"
                     "  -mmac_d16\n"
                     "  -mmin-max\n"
                     "  -mmin_max\n"
                     "  -mmul64\n"
                     "  -mno-mpy\n"
                     "  -mnorm\n"
                     "  -mrtsc\n"
                     "  -msimd\n"
                     "  -mswap\n"
                     "  -mswape\n"
                     "  -mtelephony\n"
                     "  -muser-mode-only\n"
                     "  -mxy\n"));
}

/* Find the proper relocation for the given opcode.  */

static bool
all_required_flags_present (const unsigned int *required_flags,
                            const struct arc_flags *pflags,
                            int nflg)
{
  if (!required_flags[0])
    {
      return true;
    }

  for (const unsigned int *req_flg = required_flags; *req_flg; ++req_flg)
    {
      bool found_current_flag = false;
      for (int j = 0; j < nflg; j++)
        {
          if (strcmp (pflags[j].name,
                      arc_flag_operands[*req_flg].name) == 0)
            {
              found_current_flag = true;
              break;
            }
        }
      if (!found_current_flag)
        {
          return false;
        }
    }

  return true;
}

static extended_bfd_reloc_code_real_type
find_reloc (const char *name,
	    const char *opcodename,
	    const struct arc_flags *pflags,
	    int nflg,
	    extended_bfd_reloc_code_real_type reloc)
{
  for (unsigned int i = 0; i < arc_num_equiv_tab; i++)
    {
      const struct arc_reloc_equiv_tab *r = &arc_reloc_equiv[i];

      if (strcmp (name, r->name) == 0
          && (r->mnemonic == NULL || strcmp (opcodename, r->mnemonic) == 0)
          && reloc == r->oldreloc
          && all_required_flags_present (r->flags, pflags, nflg))
        {
          return r->newreloc;
        }
    }

  as_bad (_("Unable to find %s relocation for instruction %s"),
	  name, opcodename);
  return BFD_RELOC_UNUSED;
}

/* All the symbol types that are allowed to be used for
   relaxation.  */

static bool
may_relax_expr (expressionS tok)
{
  if (tok.X_md == O_plt)
    {
      return false;
    }

  switch (tok.X_op)
    {
    case O_symbol:
    case O_multiply:
    case O_divide:
    case O_modulus:
    case O_add:
    case O_subtract:
      return true;
    default:
      return false;
    }
}

/* Checks if flags are in line with relaxable insn.  */

static bool
relaxable_flag (const struct arc_relaxable_ins *ins,
		const struct arc_flags *pflags,
		int nflgs)
{
  for (int i = 0; i < nflgs; ++i)
    {
      bool found = false;
      for (unsigned class_idx = 0; ins->flag_classes[class_idx] != 0 && !found; ++class_idx)
	{
	  unsigned flag_class = ins->flag_classes[class_idx];
	  for (unsigned flag_idx = 0; arc_flag_classes[flag_class].flags[flag_idx] != 0; ++flag_idx)
	    {
	      unsigned flag = arc_flag_classes[flag_class].flags[flag_idx];
	      const struct arc_flag_operand *flag_opand = &arc_flag_operands[flag];

	      if (strcmp (pflags[i].name, flag_opand->name) == 0)
		{
		  found = true;
		  break;
		}
	    }
	}

      if (!found)
	{
	  return false;
	}
    }

  return true;
}

/* Checks if operands are in line with relaxable insn.  */

static bool
relaxable_operand (const struct arc_relaxable_ins *ins,
		   const expressionS *tok,
		   int ntok)
{
  int i;
  for (i = 0; ins->operands[i] != EMPTY; ++i)
    {
      if (i >= ntok)
	{
	  return false;
	}

      const expressionS *epr = &tok[i];

      switch (ins->operands[i])
	{
	case IMMEDIATE:
	  switch (epr->X_op)
	    {
	    case O_multiply:
	    case O_divide:
	    case O_modulus:
	    case O_add:
	    case O_subtract:
	    case O_symbol:
	      break;
	    default:
	      return false;
	    }
	  break;

	case REGISTER_DUP:
	  if (i == 0
	      || epr->X_op != O_register
	      || epr->X_add_number != tok[i - 1].X_add_number)
	    {
	      return false;
	    }
	  break;

	case REGISTER:
	  if (epr->X_op != O_register)
	    {
	      return false;
	    }
	  break;

	case REGISTER_S:
	  {
	    const int reg_num = epr->X_add_number;
	    if (epr->X_op != O_register
		|| !((reg_num >= 0 && reg_num <= 3)
		     || (reg_num >= 12 && reg_num <= 15)))
	      {
		return false;
	      }
	  }
	  break;

	case REGISTER_NO_GP:
	  if (epr->X_op != O_register
	      || epr->X_add_number == 26) /* 26 is the gp register.  */
	    {
	      return false;
	    }
	  break;

	case BRACKET:
	  if (epr->X_op != O_bracket)
	    {
	      return false;
	    }
	  break;

	default:
	  return false;
	}
    }

  return i == ntok;
}

/* Return TRUE if this OPDCODE is a candidate for relaxation.  */

static bool
relax_insn_p (const struct arc_opcode *opcode,
	      const expressionS *tok,
	      int ntok,
	      const struct arc_flags *pflags,
	      int nflg)
{
  if (!relaxation_state)
    {
      return false;
    }

  for (unsigned i = 0; i < arc_num_relaxable_ins; ++i)
    {
      const struct arc_relaxable_ins *rlx_ins = &arc_relaxable_insns[i];

      if (strcmp (opcode->name, rlx_ins->mnemonic_r) != 0)
	{
	  continue;
	}
      if (!may_relax_expr (tok[rlx_ins->opcheckidx]))
	{
	  continue;
	}
      if (!relaxable_operand (rlx_ins, tok, ntok))
	{
	  continue;
	}
      if (!relaxable_flag (rlx_ins, pflags, nflg))
	{
	  continue;
	}

      /* All checks passed, this instruction is relaxable. */
      frag_now->fr_subtype = rlx_ins->subtype;
      frag_now->tc_frag_data.nflg = nflg;
      frag_now->tc_frag_data.ntok = ntok;
      memcpy (&frag_now->tc_frag_data.tok, tok,
	      sizeof (expressionS) * ntok);
      memcpy (&frag_now->tc_frag_data.pflags, pflags,
	      sizeof (struct arc_flags) * nflg);

      return true;
    }

  return false;
}

/* Turn an opcode description and a set of arguments into
   an instruction and a fixup.  */

static void
add_fixup (struct arc_insn *insn,
           const expressionS *exp,
           extended_bfd_reloc_code_real_type reloc,
           unsigned char pcrel,
           bool islong)
{
  if (insn->nfixups >= MAX_INSN_FIXUPS)
    as_fatal (_("too many fixups"));

  struct arc_fixup *fixup = &insn->fixups[insn->nfixups++];
  fixup->exp = *exp;
  fixup->reloc = reloc;
  fixup->pcrel = pcrel;
  fixup->islong = islong;
}

static extended_bfd_reloc_code_real_type
get_reloc_for_modifier (int mod,
                        const struct arc_opcode *opcode,
                        const struct arc_operand *operand,
                        const struct arc_flags *pflags,
                        int nflg,
                        bool *needGOTSymbol)
{
  *needGOTSymbol = false;
  switch (mod)
    {
    case O_plt:
      if (opcode->insn_class == JUMP)
        as_bad (_("Unable to use @plt relocation for insn %s"), opcode->name);
      *needGOTSymbol = true;
      return find_reloc ("plt", opcode->name, pflags, nflg, operand->default_reloc);

    case O_gotoff:
    case O_gotpc:
      *needGOTSymbol = true;
      return ARC_RELOC_TABLE (mod)->reloc;

    case O_pcl:
      if (operand->flags & ARC_OPERAND_LIMM)
        {
          if (arc_opcode_len (opcode) == 2 || opcode->insn_class == JUMP)
            as_bad (_("Unable to use @pcl relocation for insn %s"), opcode->name);
          return ARC_RELOC_TABLE (mod)->reloc;
        }
      return operand->default_reloc;

    case O_sda:
      return find_reloc ("sda", opcode->name, pflags, nflg, operand->default_reloc);

    case O_tlsgd:
    case O_tlsie:
      *needGOTSymbol = true;
      return ARC_RELOC_TABLE (mod)->reloc;

    case O_tpoff:
    case O_dtpoff:
      return ARC_RELOC_TABLE (mod)->reloc;

    case O_tpoff9:
    case O_dtpoff9:
      as_bad (_("TLS_*_S9 relocs are not supported yet"));
      return BFD_RELOC_UNUSED;

    default:
      return operand->default_reloc;
    }
}

static void
handle_arcv2_t_nt_flags (unsigned long long *image,
                         struct arc_insn *insn,
                         const struct arc_opcode *opcode,
                         const struct arc_flag_operand *flg_operand,
                         const expressionS *reloc_exp)
{
  gas_assert (reloc_exp != NULL);

  unsigned bitYoperand;
  bool is_bbit = !strcmp (opcode->name, "bbit0") || !strcmp (opcode->name, "bbit1");
  bool is_t_flag = !strcmp (flg_operand->name, "t");

  if (is_t_flag)
    bitYoperand = is_bbit ? arc_NToperand : arc_Toperand;
  else
    bitYoperand = is_bbit ? arc_Toperand : arc_NToperand;

  if (reloc_exp->X_op == O_constant)
    {
      offsetT val = reloc_exp->X_add_number;
      *image |= insert_operand (*image, &arc_operands[bitYoperand], val, NULL, 0);
    }
  else
    {
      unsigned char pcrel = 0;
      if (insn->nfixups > 0)
        pcrel = insn->fixups[insn->nfixups - 1].pcrel;

      add_fixup (insn, reloc_exp, -bitYoperand, pcrel, false);
    }
}

static void
update_and_check_insn_flow (const struct arc_opcode *opcode,
                            const struct arc_insn *insn,
                            bool has_delay_slot)
{
  if (arc_last_insns[1].has_delay_slot)
    {
      if (is_br_jmp_insn_p (opcode))
        as_bad (_("Insn %s has a jump/branch instruction %s in its delay slot."),
                arc_last_insns[1].opcode->name,
                opcode->name);
      if (insn->has_limm)
        as_bad (_("Insn %s has an instruction %s with limm in its delay slot."),
                arc_last_insns[1].opcode->name,
                opcode->name);
    }

  arc_last_insns[1] = arc_last_insns[0];
  arc_last_insns[0].opcode = opcode;
  arc_last_insns[0].has_limm = insn->has_limm;
  arc_last_insns[0].has_delay_slot = has_delay_slot;
}

static void
assemble_insn (const struct arc_opcode *opcode,
	       const expressionS *tok,
	       int ntok,
	       const struct arc_flags *pflags,
	       int nflg,
	       struct arc_insn *insn)
{
  const expressionS *reloc_exp = NULL;
  unsigned long long image = opcode->opcode;
  bool has_delay_slot = false;
  int tokidx = 0;

  memset (insn, 0, sizeof (*insn));

  pr_debug ("%s:%d: assemble_insn: %s using opcode %llx\n",
	    frag_now->fr_file, frag_now->fr_line, opcode->name,
	    opcode->opcode);

  for (const unsigned char *argidx = opcode->operands; *argidx; ++argidx)
    {
      const struct arc_operand *operand = &arc_operands[*argidx];
      if (ARC_OPERAND_IS_FAKE (operand))
	    continue;

      if (operand->flags & ARC_OPERAND_DUPLICATE)
	{
	  tokidx++;
	  continue;
	}

      if (tokidx >= ntok)
	    as_fatal (_("Internal error: operand token missing for %s"), opcode->name);

      const expressionS *t = &tok[tokidx++];
      if (operand->flags & ARC_OPERAND_LIMM)
	    insn->has_limm = true;

      switch (t->X_op)
	{
	case O_register:
	  image = insert_operand (image, operand, regno (t->X_add_number), NULL, 0);
	  break;
	case O_constant:
	  image = insert_operand (image, operand, t->X_add_number, NULL, 0);
	  if (operand->flags & ARC_OPERAND_LIMM)
	    insn->limm = t->X_add_number;
	  reloc_exp = t;
	  break;
	case O_bracket:
	case O_colon:
	case O_addrtype:
	  break;
	case O_absent:
	  gas_assert (operand->flags & ARC_OPERAND_IGNORE);
	  break;
	case O_subtract:
	  if ((t->X_add_number == 0)
	      && contains_register (t->X_add_symbol)
	      && contains_register (t->X_op_symbol))
	    {
	      int regs = (get_register (t->X_add_symbol) << 16) | get_register (t->X_op_symbol);
	      image = insert_operand (image, operand, regs, NULL, 0);
	      break;
	    }
	default:
	  {
	    bool needGOTSymbol;
	    extended_bfd_reloc_code_real_type reloc =
	      get_reloc_for_modifier (t->X_md, opcode, operand, pflags, nflg, &needGOTSymbol);

	    if (needGOTSymbol && (GOT_symbol == NULL))
	      GOT_symbol = symbol_find_or_make (GLOBAL_OFFSET_TABLE_NAME);

	    unsigned char pcrel;
	    if ((int) reloc < 0)
	      {
		pcrel = (operand->flags & ARC_OPERAND_PCREL) ? 1 : 0;
	      }
	    else
	      {
		reloc_howto_type *howto = bfd_reloc_type_lookup (stdoutput, reloc);
		pcrel = howto ? howto->pc_relative : 0;
	      }
	    add_fixup (insn, t, reloc, pcrel, (operand->flags & ARC_OPERAND_LIMM) != 0);
	    reloc_exp = t;
	  }
	  break;
	}
    }

  for (int i = 0; i < nflg; i++)
    {
      const struct arc_flag_operand *flg_operand = pflags[i].flgp;
      if (!strcmp (flg_operand->name, "d"))
	    has_delay_slot = true;

      bool is_t_or_nt = !strcmp (flg_operand->name, "t") || !strcmp (flg_operand->name, "nt");
      if ((selected_cpu.flags & ARC_OPCODE_ARCV2) && is_t_or_nt)
	{
	  handle_arcv2_t_nt_flags (&image, insn, opcode, flg_operand, reloc_exp);
	}
      else
	{
	  image |= (flg_operand->code & ((1ULL << flg_operand->bits) - 1)) << flg_operand->shift;
	}
    }

  insn->relax = relax_insn_p (opcode, tok, ntok, pflags, nflg);
  insn->len = arc_opcode_len (opcode);
  insn->insn = image;

  update_and_check_insn_flow (opcode, insn, has_delay_slot);
}

void
arc_handle_align (fragS *fragP)
{
  if (!fragP || !fragP->fr_next)
    {
      return;
    }

  if (fragP->fr_type != rs_align_code)
    {
      return;
    }

  const valueT current_pos = fragP->fr_address + fragP->fr_fix;
  if (fragP->fr_next->fr_address < current_pos)
    {
      return;
    }

  const valueT gap_size = fragP->fr_next->fr_address - current_pos;
  char *dest = fragP->fr_literal + fragP->fr_fix;
  const int alignment_size = 2;

  fragP->fr_var = alignment_size;

  if ((gap_size % alignment_size) != 0)
    {
      fragP->fr_fix++;
      *dest++ = 0;
    }

  md_number_to_chars (dest, NOP_OPCODE_S, alignment_size);
}

/* Here we decide which fixups can be adjusted to make them relative
   to the beginning of the section instead of the symbol.  Basically
   we need to make sure that the dynamic relocations are done
   correctly, so in some cases we force the original symbol to be
   used.  */

int
tc_arc_fix_adjustable (fixS *fixP)
{
  if (!fixP || S_IS_EXTERNAL (fixP->fx_addsy) || S_IS_WEAK (fixP->fx_addsy))
    {
      return 0;
    }

  switch (fixP->fx_r_type)
    {
    case BFD_RELOC_ARC_GOTPC32:
    case BFD_RELOC_ARC_PLT32:
    case BFD_RELOC_ARC_S25H_PCREL_PLT:
    case BFD_RELOC_ARC_S21H_PCREL_PLT:
    case BFD_RELOC_ARC_S25W_PCREL_PLT:
    case BFD_RELOC_ARC_S21W_PCREL_PLT:
      return 0;
    default:
      return 1;
    }
}

/* Compute the reloc type of an expression EXP.  */

static void
arc_check_reloc (expressionS *exp,
                 bfd_reloc_code_real_type *r_type_p)
{
  if (exp == NULL || r_type_p == NULL)
    {
      return;
    }

  if (*r_type_p != BFD_RELOC_32)
    {
      return;
    }

  if (exp->X_op != O_subtract)
    {
      return;
    }

  if (exp->X_op_symbol == NULL)
    {
      return;
    }

  if (S_GET_SEGMENT (exp->X_op_symbol) == now_seg)
    {
      *r_type_p = BFD_RELOC_ARC_32_PCREL;
    }
}


/* Add expression EXP of SIZE bytes to offset OFF of fragment FRAG.  */

void
arc_cons_fix_new (fragS *frag, int off, int size, expressionS *exp)
{
  bfd_reloc_code_real_type r_type;

  switch (size)
    {
    case 1:
      r_type = BFD_RELOC_8;
      break;

    case 2:
      r_type = BFD_RELOC_16;
      break;

    case 3:
      r_type = BFD_RELOC_24;
      break;

    case 4:
      r_type = BFD_RELOC_32;
      arc_check_reloc (exp, &r_type);
      break;

    case 8:
      r_type = BFD_RELOC_64;
      break;

    default:
      as_bad (_("unsupported BFD relocation size %u"), (unsigned int) size);
      r_type = BFD_RELOC_UNUSED;
      break;
    }

  fix_new_exp (frag, off, size, exp, 0, r_type);
}

/* The actual routine that checks the ZOL conditions.  */

static void
check_zol (symbolS *s)
{
  const char *s_name = S_GET_NAME (s);

  switch (selected_cpu.mach)
    {
    case bfd_mach_arc_arcv2:
      if (selected_cpu.flags & ARC_OPCODE_ARCv2EM)
        {
          return;
        }

      if (is_br_jmp_insn_p (arc_last_insns[0].opcode)
          || arc_last_insns[1].has_delay_slot)
        {
          as_bad (_("Jump/Branch instruction detected at the end of the ZOL label @%s"),
                  s_name);
        }
      break;

    case bfd_mach_arc_arc600:
    case bfd_mach_arc_arc700:
      if (selected_cpu.mach == bfd_mach_arc_arc600)
        {
          if (is_kernel_insn_p (arc_last_insns[0].opcode))
            {
              as_bad (_("Kernel instruction detected at the end of the ZOL label @%s"),
                      s_name);
            }

          if (arc_last_insns[0].has_limm
              && is_br_jmp_insn_p (arc_last_insns[0].opcode))
            {
              as_bad (_("A jump instruction with long immediate detected at the end of the ZOL label @%s"),
                      s_name);
            }
        }

      if (arc_last_insns[0].has_delay_slot)
        {
          as_bad (_("An illegal use of delay slot detected at the end of the ZOL label @%s"),
                  s_name);
        }
      break;

    default:
      break;
    }
}

/* If ZOL end check the last two instruction for illegals.  */
void
arc_frob_label (symbolS * sym)
{
  if (!sym)
    {
      return;
    }

  if ((ARC_GET_FLAG (sym) & ARC_FLAG_ZOL) != 0)
    {
      check_zol (sym);
    }

  dwarf2_emit_label (sym);
}

/* Used because generic relaxation assumes a pc-rel value whilst we
   also relax instructions that use an absolute value resolved out of
   relative values (if that makes any sense).  An example: 'add r1,
   r2, @.L2 - .'  The symbols . and @.L2 are relative to the section
   but if they're in the same section we can subtract the section
   offset relocation which ends up in a resolved value.  So if @.L2 is
   .text + 0x50 and . is .text + 0x10, we can say that .text + 0x50 -
   .text + 0x40 = 0x10.  */
int
arc_pcrel_adjust (fragS *fragP)
{
  if (!fragP)
    {
      return 0;
    }

  pr_debug ("arc_pcrel_adjust: address=%ld, fix=%ld, PCrel %s\n",
            fragP->fr_address, fragP->fr_fix,
            fragP->tc_frag_data.pcrel ? "Y" : "N");

  static const int PCL_LOWER_BITS_MASK = 0x03;
  const long target_address = fragP->fr_address + fragP->fr_fix;

  if (fragP->tc_frag_data.pcrel)
    {
      return target_address & PCL_LOWER_BITS_MASK;
    }

  return target_address;
}

/* Initialize the DWARF-2 unwind information for this procedure.  */

#define ARC_STACK_POINTER_REGNUM 28
#define INITIAL_CFA_OFFSET 0

void
tc_arc_frame_initial_instructions (void)
{
  cfi_add_CFA_def_cfa (ARC_STACK_POINTER_REGNUM, INITIAL_CFA_OFFSET);
}

int
tc_arc_regname_to_dw2regnum (const char *regname)
{
  if (!regname)
    {
      return -1;
    }

  struct symbol *sym = str_hash_find (arc_reg_hash, regname);
  return sym ? S_GET_VALUE (sym) : -1;
}

/* Adjust the symbol table.  Delete found AUX register symbols.  */

void
arc_adjust_symtab (void)
{
  symbolS *sym = symbol_rootP;
  symbolS *next_sym;

  while (sym != NULL)
    {
      next_sym = symbol_next (sym);

      if (ARC_GET_FLAG (sym) & ARC_FLAG_AUX)
	{
	  symbol_remove (sym, &symbol_rootP, &symbol_lastP);
	}
      sym = next_sym;
    }

  elf_adjust_symtab ();
}

#include <stdbool.h>
#include <ctype.h>

/* Forward declaration of the attribute struct type. */
struct attribute_def;

static bool
expect_comma (const char *error_msg)
{
  SKIP_WHITESPACE ();
  if (*input_line_pointer != ',')
    {
      as_bad (error_msg);
      ignore_rest_of_line ();
      return false;
    }
  input_line_pointer++;
  return true;
}

static bool
parse_attribute_from_table (unsigned char *target_value,
                            const struct attribute_def *table,
                            size_t table_size)
{
  for (size_t i = 0; i < table_size; i++)
    {
      if (!strncmp (table[i].name, input_line_pointer, table[i].len))
	{
	  *target_value |= table[i].attr_class;
	  input_line_pointer += table[i].len;
	  return true;
	}
    }
  return false;
}

static bool
parse_suffix_class_list (unsigned char *suffix_class)
{
  while (true)
    {
      SKIP_WHITESPACE ();
      if (!parse_attribute_from_table (suffix_class, suffixclass,
				       ARRAY_SIZE (suffixclass)))
	{
	  as_bad ("invalid suffix class");
	  ignore_rest_of_line ();
	  return false;
	}

      SKIP_WHITESPACE ();
      if (*input_line_pointer != '|')
	{
	  break;
	}
      input_line_pointer++;
    }
  return true;
}

static bool
parse_syntax_components_list (unsigned char *syntax_class,
                              unsigned char *syntax_class_modifiers)
{
  while (true)
    {
      SKIP_WHITESPACE ();
      bool found = parse_attribute_from_table (syntax_class_modifiers,
					       syntaxclassmod,
					       ARRAY_SIZE (syntaxclassmod));
      if (!found)
	{
	  found = parse_attribute_from_table (syntax_class, syntaxclass,
					      ARRAY_SIZE (syntaxclass));
	}

      if (!found)
	{
	  as_bad ("missing or invalid syntax class/modifier");
	  ignore_rest_of_line ();
	  return false;
	}

      SKIP_WHITESPACE ();
      if (*input_line_pointer != '|')
	{
	  break;
	}
      input_line_pointer++;
    }
  return true;
}

static void
tokenize_extinsn (extInstruction_t *einsn)
{
  char *p, c;
  char *insn_name;
  unsigned char major_opcode;
  unsigned char sub_opcode;
  unsigned char syntax_class = 0;
  unsigned char syntax_class_modifiers = 0;
  unsigned char suffix_class = 0;

  SKIP_WHITESPACE ();

  p = input_line_pointer;
  c = get_symbol_name (&p);
  insn_name = xstrdup (p);
  restore_line_pointer (c);

  for (p = insn_name; *p; ++p)
    *p = tolower (*p);

  if (!expect_comma (_("expected comma after instruction name")))
    {
      free (insn_name);
      return;
    }
  major_opcode = get_absolute_expression ();

  if (!expect_comma (_("expected comma after major opcode")))
    {
      free (insn_name);
      return;
    }
  sub_opcode = get_absolute_expression ();

  if (!expect_comma ("expected comma after sub opcode"))
    {
      free (insn_name);
      return;
    }
  if (!parse_suffix_class_list (&suffix_class))
    {
      free (insn_name);
      return;
    }

  if (!expect_comma ("expected comma after suffix class"))
    {
      free (insn_name);
      return;
    }
  if (!parse_syntax_components_list (&syntax_class, &syntax_class_modifiers))
    {
      free (insn_name);
      return;
    }

  demand_empty_rest_of_line ();

  einsn->name   = insn_name;
  einsn->major  = major_opcode;
  einsn->minor  = sub_opcode;
  einsn->syntax = syntax_class;
  einsn->modsyn = syntax_class_modifiers;
  einsn->suffix = suffix_class;
  einsn->flags  = syntax_class
    | (syntax_class_modifiers & ARC_OP1_IMM_IMPLIED ? 0x10 : 0);
}

/* Generate an extension section.  */

static int
arc_set_ext_seg (void)
{
  if (arcext_section)
    {
      subseg_set (arcext_section, 0);
      return 1;
    }

  arcext_section = subseg_new (".arcextmap", 0);
  if (!arcext_section)
    {
      return 0;
    }

  bfd_set_section_flags (arcext_section, SEC_READONLY | SEC_HAS_CONTENTS);
  return 1;
}

/* Create an extension instruction description in the arc extension
   section of the output file.
   The structure for an instruction is like this:
   [0]: Length of the record.
   [1]: Type of the record.

   [2]: Major opcode.
   [3]: Sub-opcode.
   [4]: Syntax (flags).
   [5]+ Name instruction.

   The sequence is terminated by an empty entry.  */

static void
create_extinst_section (extInstruction_t *einsn)
{
  if (!einsn || !einsn->name)
    {
      return;
    }

  const segT old_sec = now_seg;
  const int old_subsec = now_subseg;
  const size_t name_len = strlen (einsn->name);
  const size_t total_size = 5 + name_len + 1;

  if (total_size > UCHAR_MAX)
    {
      return;
    }

  arc_set_ext_seg ();

  char *p = frag_more (total_size);
  if (!p)
    {
      subseg_set (old_sec, old_subsec);
      return;
    }

  *p++ = (unsigned char) total_size;
  *p++ = EXT_INSTRUCTION;
  *p++ = einsn->major;
  *p++ = einsn->minor;
  *p++ = einsn->flags;
  memcpy (p, einsn->name, name_len + 1);

  subseg_set (old_sec, old_subsec);
}

/* Handler .extinstruction pseudo-op.  */

static void
validate_opcode_range (const extInstruction_t *einsn, unsigned long cpu_flags)
{
  const unsigned char moplow = 0x05;
  const unsigned char mophigh = (cpu_flags & (ARC_OPCODE_ARCv2EM | ARC_OPCODE_ARCv2HS))
                              ? 0x07
                              : 0x0a;

  if (einsn->major < moplow || einsn->major > mophigh)
    {
      as_fatal (_("major opcode not in range [0x%02x - 0x%02x]"), moplow, mophigh);
    }

  const bool is_minor_range_exempt = (einsn->major == 5
                                      || einsn->major == 9
                                      || einsn->major == 0x0a);
  if (einsn->minor > 0x3f && !is_minor_range_exempt)
    {
      as_fatal (_("minor opcode not in range [0x00 - 0x3f]"));
    }
}

static void
validate_syntax_modifiers (const extInstruction_t *einsn)
{
  switch (einsn->syntax & ARC_SYNTAX_MASK)
    {
    case ARC_SYNTAX_3OP:
      if (einsn->modsyn & ARC_OP1_IMM_IMPLIED)
        {
          as_fatal (_("Improper use of OP1_IMM_IMPLIED"));
        }
      break;

    case ARC_SYNTAX_2OP:
    case ARC_SYNTAX_1OP:
    case ARC_SYNTAX_NOP:
      if (einsn->modsyn & ARC_OP1_MUST_BE_IMM)
        {
          as_fatal (_("Improper use of OP1_MUST_BE_IMM"));
        }
      break;

    default:
      break;
    }
}

static void
arc_extinsn (int ignore ATTRIBUTE_UNUSED)
{
  extInstruction_t einsn;
  memset (&einsn, 0, sizeof (einsn));
  tokenize_extinsn (&einsn);

  if (arc_find_opcode (einsn.name))
    {
      as_warn (_("Pseudocode already used %s"), einsn.name);
    }

  validate_opcode_range (&einsn, selected_cpu.flags);
  validate_syntax_modifiers (&einsn);

  const char *errmsg = NULL;
  struct arc_opcode *arc_ext_opcodes =
    arcExtMap_genOpcode (&einsn, selected_cpu.flags, &errmsg);

  if (arc_ext_opcodes == NULL)
    {
      as_fatal ("%s", errmsg
                      ? errmsg
                      : _("Couldn't generate extension instruction opcodes"));
    }
  else if (errmsg)
    {
      as_warn ("%s", errmsg);
    }

  arc_insert_opcode (arc_ext_opcodes);
  create_extinst_section (&einsn);
}

static bool
tokenize_extregister (extRegister_t *ereg, int opertype)
{
  char *name = NULL;
  char *p;
  char c;
  int number;
  int imode = 0;

  /* 1st: get register name.  */
  SKIP_WHITESPACE ();
  p = input_line_pointer;
  c = get_symbol_name (&p);

  name = xstrdup (p);
  restore_line_pointer (c);

  /* 2nd: get register number.  */
  SKIP_WHITESPACE ();

  if (*input_line_pointer++ != ',')
    {
      as_bad (_("expected comma after name"));
      goto fail;
    }
  number = get_absolute_expression ();

  if ((number < 0) && (opertype != EXT_AUX_REGISTER))
    {
      as_bad (_("%s second argument cannot be a negative number %d"),
	      (opertype == EXT_CORE_REGISTER) ? "extCoreRegister's" : "extCondCode's",
	      number);
      goto fail;
    }

  if (opertype == EXT_CORE_REGISTER || opertype == EXT_AUX_REGISTER)
    {
      /* 3rd: get register mode.  */
      char *mode;
      SKIP_WHITESPACE ();

      if (*input_line_pointer++ != ',')
	{
	  as_bad (_("expected comma after register number"));
	  goto fail;
	}

      mode = input_line_pointer;
      if (startswith (mode, "r|w"))
	{
	  imode = 0;
	  input_line_pointer += 3;
	}
      else if (startswith (mode, "r"))
	{
	  imode = ARC_REGISTER_READONLY;
	  input_line_pointer += 1;
	}
      else if (startswith (mode, "w"))
	{
	  imode = ARC_REGISTER_WRITEONLY;
	  input_line_pointer += 1;
	}
      else
	{
	  as_bad (_("invalid mode"));
	  goto fail;
	}
    }

  if (opertype == EXT_CORE_REGISTER)
    {
      /* 4th: get core register shortcut.  */
      SKIP_WHITESPACE ();
      if (*input_line_pointer++ != ',')
	{
	  as_bad (_("expected comma after register mode"));
	  goto fail;
	}

      if (startswith (input_line_pointer, "cannot_shortcut"))
	{
	  imode |= ARC_REGISTER_NOSHORT_CUT;
	  input_line_pointer += 15;
	}
      else if (startswith (input_line_pointer, "can_shortcut"))
	{
	  input_line_pointer += 12;
	}
      else
	{
	  as_bad (_("shortcut designator invalid"));
	  goto fail;
	}
    }

  demand_empty_rest_of_line ();

  ereg->name = name;
  ereg->number = number;
  ereg->imode  = imode;
  return true;

fail:
  ignore_rest_of_line ();
  free (name);
  return false;
}

/* Create an extension register/condition description in the arc
   extension section of the output file.

   The structure for an instruction is like this:
   [0]: Length of the record.
   [1]: Type of the record.

   For core regs and condition codes:
   [2]: Value.
   [3]+ Name.

   For auxiliary registers:
   [2..5]: Value.
   [6]+ Name

   The sequence is terminated by an empty entry.  */

static void
create_extcore_section (extRegister_t *ereg, int opertype)
{
  segT old_sec = now_seg;
  int old_subsec = now_subseg;
  size_t name_len = strlen (ereg->name);
  unsigned char header[6];
  size_t header_len = 0;

  arc_set_ext_seg ();

  switch (opertype)
    {
    case EXT_COND_CODE:
    case EXT_CORE_REGISTER:
      header_len = 3;
      header[0] = header_len + name_len + 1;
      header[1] = (unsigned char) opertype;
      header[2] = (unsigned char) ereg->number;
      break;

    case EXT_AUX_REGISTER:
      header_len = 6;
      unsigned int num = ereg->number;
      header[0] = header_len + name_len + 1;
      header[1] = (unsigned char) EXT_AUX_REGISTER;
      header[2] = (num >> 24) & 0xff;
      header[3] = (num >> 16) & 0xff;
      header[4] = (num >> 8) & 0xff;
      header[5] = num & 0xff;
      break;

    default:
      break;
    }

  if (header_len > 0)
    {
      char *p = frag_more (header_len + name_len + 1);
      memcpy (p, header, header_len);
      memcpy (p + header_len, ereg->name, name_len + 1);
    }

  subseg_set (old_sec, old_subsec);
}

/* Handler .extCoreRegister pseudo-op.  */

static void
handle_core_register (const extRegister_t *ereg)
{
  const int MAX_CORE_REG_VALUE = 60;
  if (ereg->number > MAX_CORE_REG_VALUE)
    {
      as_bad (_("core register %s value (%d) too large"), ereg->name,
	      ereg->number);
    }
  declare_register (ereg->name, ereg->number);
}

static void
handle_aux_register (const extRegister_t *ereg)
{
  struct arc_aux_reg *auxr = XNEW (struct arc_aux_reg);
  auxr->name = ereg->name;
  auxr->cpu = selected_cpu.flags;
  auxr->subclass = NONE;
  auxr->address = ereg->number;
  if (str_hash_insert (arc_aux_hash, auxr->name, auxr, 0) != NULL)
    {
      as_bad (_("duplicate aux register %s"), auxr->name);
    }
}

static void
handle_cond_code (const extRegister_t *ereg)
{
  const int MAX_COND_CODE_VALUE = 31;
  const int COND_CODE_BITS = 5;
  const int COND_CODE_SHIFT = 0;

  if (ereg->number > MAX_COND_CODE_VALUE)
    {
      as_bad (_("condition code %s value (%d) too large"), ereg->name,
	      ereg->number);
      return;
    }

  size_t old_size = ext_condcode.size;
  size_t new_capacity = old_size + 2;

  ext_condcode.arc_ext_condcode =
    XRESIZEVEC (struct arc_flag_operand, ext_condcode.arc_ext_condcode,
		new_capacity);

  struct arc_flag_operand *ccode = &ext_condcode.arc_ext_condcode[old_size];
  ccode->name = ereg->name;
  ccode->code = ereg->number;
  ccode->bits = COND_CODE_BITS;
  ccode->shift = COND_CODE_SHIFT;
  ccode->favail = 0;

  memset (&ext_condcode.arc_ext_condcode[old_size + 1], 0,
	  sizeof (struct arc_flag_operand));

  ext_condcode.size++;
}

static void
arc_extcorereg (int opertype)
{
  extRegister_t ereg;

  memset (&ereg, 0, sizeof (ereg));
  if (!tokenize_extregister (&ereg, opertype))
    {
      return;
    }

  switch (opertype)
    {
    case EXT_CORE_REGISTER:
      handle_core_register (&ereg);
      break;
    case EXT_AUX_REGISTER:
      handle_aux_register (&ereg);
      break;
    case EXT_COND_CODE:
      handle_cond_code (&ereg);
      break;
    default:
      as_bad (_("Unknown extension"));
      return;
    }

  create_extcore_section (&ereg, opertype);
}

/* Parse a .arc_attribute directive.  */

static void
arc_attribute (int ignored ATTRIBUTE_UNUSED)
{
  int tag = obj_elf_vendor_attribute (OBJ_ATTR_PROC);

  if (tag >= 0 && tag < NUM_KNOWN_OBJ_ATTRIBUTES)
    {
      attributes_set_explicitly[tag] = true;
    }
}

/* Set an attribute if it has not already been set by the user.  */

static void
arc_set_attribute_int (int tag, int value)
{
  const bool is_known_and_set = tag >= 1
                                && tag < NUM_KNOWN_OBJ_ATTRIBUTES
                                && attributes_set_explicitly[tag];

  if (is_known_and_set)
    {
      return;
    }

  if (!bfd_elf_add_proc_attr_int (stdoutput, tag, value))
    {
      as_fatal (_("error adding attribute: %s"),
                bfd_errmsg (bfd_get_error ()));
    }
}

static void
arc_set_attribute_string (int tag, const char *value)
{
  if (tag >= 1
      && tag < NUM_KNOWN_OBJ_ATTRIBUTES
      && attributes_set_explicitly[tag])
    {
      return;
    }

  if (!bfd_elf_add_proc_attr_string (stdoutput, tag, value))
    {
      as_fatal (_("error adding attribute: %s"),
		bfd_errmsg (bfd_get_error ()));
    }
}

/* Allocate and concatenate two strings.  s1 can be NULL but not
   s2.  s1 pointer is freed at end of this procedure.  */

static char *
arc_stralloc (char * s1, const char * s2)
{
  gas_assert (s2 != NULL);

  if (s1 == NULL)
    {
      size_t s2_len = strlen (s2);
      char *p = xmalloc (s2_len + 1);
      memcpy (p, s2, s2_len + 1);
      return p;
    }

  size_t s1_len = strlen (s1);
  size_t s2_len = strlen (s2);
  size_t new_len = s1_len + 1 + s2_len + 1;
  char *p = xmalloc (new_len);

  snprintf (p, new_len, "%s,%s", s1, s2);

  free (s1);
  return p;
}

/* Set the public ARC object attributes.  */

static int
get_cpu_base_tag (void)
{
  switch (selected_cpu.eflags & EF_ARC_MACH_MSK)
    {
    case E_ARC_MACH_ARC600:
    case E_ARC_MACH_ARC601:
      return TAG_CPU_ARC6xx;
    case E_ARC_MACH_ARC700:
      return TAG_CPU_ARC7xx;
    case EF_ARC_CPU_ARCV2EM:
      return TAG_CPU_ARCEM;
    case EF_ARC_CPU_ARCV2HS:
      return TAG_CPU_ARCHS;
    default:
      return 0;
    }
}

static void
add_proc_attr_int_or_fatal (int tag, int value)
{
  if (!bfd_elf_add_proc_attr_int (stdoutput, tag, value))
    as_fatal (_("error adding attribute: %s"),
	      bfd_errmsg (bfd_get_error ()));
}

static void
set_cpu_base_attribute (void)
{
  const int base = get_cpu_base_tag ();

  if (attributes_set_explicitly[Tag_ARC_CPU_base]
      && (base != bfd_elf_get_obj_attr_int (stdoutput, OBJ_ATTR_PROC,
					    Tag_ARC_CPU_base)))
    as_warn (_("Overwrite explicitly set Tag_ARC_CPU_base"));

  add_proc_attr_int_or_fatal (Tag_ARC_CPU_base, base);
}

static void
set_os_abi_version_attribute (void)
{
  if (attributes_set_explicitly[Tag_ARC_ABI_osver])
    {
      const int val = bfd_elf_get_obj_attr_int (stdoutput, OBJ_ATTR_PROC,
						Tag_ARC_ABI_osver);

      selected_cpu.eflags = ((selected_cpu.eflags & ~EF_ARC_OSABI_MSK)
			     | ((val & 0x0f) << 8));
    }
  else
    {
      arc_set_attribute_int (Tag_ARC_ABI_osver, E_ARC_OSABI_CURRENT >> 8);
    }
}

static char *
build_isa_config_string (void)
{
  char *s = NULL;
  for (unsigned int i = 0; i < ARRAY_SIZE (feature_list); i++)
    {
      if (selected_cpu.features & feature_list[i].feature)
	{
	  s = arc_stralloc (s, feature_list[i].attr);
	}
    }
  return s;
}

static void
set_isa_config_attribute (void)
{
  arc_check_feature ();
  char *isa_config_str = build_isa_config_string ();
  if (isa_config_str)
    {
      arc_set_attribute_string (Tag_ARC_ISA_config, isa_config_str);
    }
}

static void
handle_rf16_attribute_override (void)
{
  const bool user_sets_rf16 =
    attributes_set_explicitly[Tag_ARC_ABI_rf16]
    && (bfd_elf_get_obj_attr_int (stdoutput, OBJ_ATTR_PROC,
				  Tag_ARC_ABI_rf16) != 0);

  if (user_sets_rf16 && !rf16_only)
    {
      as_warn (_("Overwrite explicitly set Tag_ARC_ABI_rf16 to full "
		 "register file"));
      add_proc_attr_int_or_fatal (Tag_ARC_ABI_rf16, 0);
    }
}

static void
arc_set_public_attributes (void)
{
  /* Tag_ARC_CPU_name.  */
  arc_set_attribute_string (Tag_ARC_CPU_name, selected_cpu.name);

  /* Tag_ARC_CPU_base.  */
  set_cpu_base_attribute ();

  /* Tag_ARC_ABI_osver.  */
  set_os_abi_version_attribute ();

  /* Tag_ARC_ISA_config.  */
  set_isa_config_attribute ();

  /* Tag_ARC_ISA_mpy_option.  */
  arc_set_attribute_int (Tag_ARC_ISA_mpy_option, mpy_option);

  /* Tag_ARC_ABI_pic.  */
  arc_set_attribute_int (Tag_ARC_ABI_pic, pic_option);

  /* Tag_ARC_ABI_sda.  */
  arc_set_attribute_int (Tag_ARC_ABI_sda, sda_option);

  /* Tag_ARC_ABI_tls.  */
  arc_set_attribute_int (Tag_ARC_ABI_tls, tls_option);

  /* Tag_ARC_ATR_version.  */
  arc_set_attribute_int (Tag_ARC_ATR_version, 1);

  /* Tag_ARC_ABI_rf16.  */
  handle_rf16_attribute_override ();
}

/* Add the default contents for the .ARC.attributes section.  */

void
arc_md_finish (void)
{
  arc_set_public_attributes ();

  if (!bfd_set_arch_mach (stdoutput, bfd_arch_arc, selected_cpu.mach))
    {
      as_fatal (_("could not set architecture and machine"));
    }

  bfd_set_private_flags (stdoutput, selected_cpu.eflags);
}

void arc_copy_symbol_attributes(symbolS *dest, const symbolS *src)
{
    if (dest && src)
    {
        ARC_GET_FLAG(dest) = ARC_GET_FLAG(src);
    }
}

typedef struct
{
  const char * const name;
  const int tag;
} arc_attribute_map_entry;

static const arc_attribute_map_entry ARC_ATTRIBUTE_MAP[] =
{
  { "Tag_ARC_PCS_config", Tag_ARC_PCS_config },
  { "Tag_ARC_CPU_base", Tag_ARC_CPU_base },
  { "Tag_ARC_CPU_variation", Tag_ARC_CPU_variation },
  { "Tag_ARC_CPU_name", Tag_ARC_CPU_name },
  { "Tag_ARC_ABI_rf16", Tag_ARC_ABI_rf16 },
  { "Tag_ARC_ABI_osver", Tag_ARC_ABI_osver },
  { "Tag_ARC_ABI_sda", Tag_ARC_ABI_sda },
  { "Tag_ARC_ABI_pic", Tag_ARC_ABI_pic },
  { "Tag_ARC_ABI_tls", Tag_ARC_ABI_tls },
  { "Tag_ARC_ABI_enumsize", Tag_ARC_ABI_enumsize },
  { "Tag_ARC_ABI_exceptions", Tag_ARC_ABI_exceptions },
  { "Tag_ARC_ABI_double_size", Tag_ARC_ABI_double_size },
  { "Tag_ARC_ISA_config", Tag_ARC_ISA_config },
  { "Tag_ARC_ISA_apex", Tag_ARC_ISA_apex },
  { "Tag_ARC_ISA_mpy_option", Tag_ARC_ISA_mpy_option },
  { "Tag_ARC_ATR_version", Tag_ARC_ATR_version }
};

int arc_convert_symbolic_attribute (const char *name)
{
  if (name == NULL)
  {
    return -1;
  }

  for (size_t i = 0; i < ARRAY_SIZE (ARC_ATTRIBUTE_MAP); i++)
  {
    if (strcmp (name, ARC_ATTRIBUTE_MAP[i].name) == 0)
    {
      return ARC_ATTRIBUTE_MAP[i].tag;
    }
  }

  return -1;
}

/* Local variables:
   eval: (c-set-style "gnu")
   indent-tabs-mode: t
   End:  */
