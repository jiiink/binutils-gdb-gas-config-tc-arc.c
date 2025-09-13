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
  if (name == NULL || arc_opcode_hash == NULL)
    return NULL;
    
  return str_hash_find (arc_opcode_hash, name);
}

/* Initialise the iterator ITER.  */

static void
arc_opcode_hash_entry_iterator_init (struct arc_opcode_hash_entry_iterator *iter)
{
  if (iter == NULL)
    return;
    
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
  if (entry == NULL || iter == NULL || entry->count == 0)
    return NULL;

  if (iter->opcode == NULL)
    {
      if (iter->index >= entry->count)
        return NULL;
      
      iter->opcode = entry->opcode[iter->index];
      return iter->opcode;
    }

  const char *current_name = iter->opcode->name;
  if (current_name == NULL)
    return NULL;

  iter->opcode++;
  
  if (iter->opcode->name == NULL || strcmp(current_name, iter->opcode->name) != 0)
    {
      iter->index++;
      if (iter->index >= entry->count)
        {
          iter->opcode = NULL;
          return NULL;
        }
      iter->opcode = entry->opcode[iter->index];
    }

  return iter->opcode;
}

/* Insert an opcode into opcode hash structure.  */

static void
arc_insert_opcode (const struct arc_opcode *opcode)
{
  struct arc_opcode_hash_entry *entry;
  
  if (opcode == NULL || opcode->name == NULL)
    return;

  entry = str_hash_find (arc_opcode_hash, opcode->name);
  if (entry == NULL)
    {
      entry = XNEW (struct arc_opcode_hash_entry);
      if (entry == NULL)
        as_fatal (_("memory allocation failed"));
      
      entry->count = 0;
      entry->opcode = NULL;

      if (str_hash_insert (arc_opcode_hash, opcode->name, entry, 0) != NULL)
        {
          free (entry);
          as_fatal (_("duplicate %s"), opcode->name);
        }
    }

  const struct arc_opcode **new_opcode_array = 
    XRESIZEVEC (const struct arc_opcode *, entry->opcode, entry->count + 1);
  
  if (new_opcode_array == NULL)
    as_fatal (_("memory allocation failed"));
  
  entry->opcode = new_opcode_array;
  entry->opcode[entry->count] = opcode;
  entry->count++;
}

static void arc_opcode_free(void *elt)
{
    if (elt == NULL) {
        return;
    }
    
    string_tuple_t *tuple = elt;
    if (tuple->value != NULL) {
        struct arc_opcode_hash_entry *entry = (struct arc_opcode_hash_entry *)tuple->value;
        if (entry->opcode != NULL) {
            free(entry->opcode);
            entry->opcode = NULL;
        }
        free(entry);
        tuple->value = NULL;
    }
    free(tuple);
}

/* Like md_number_to_chars but for middle-endian values.  The 4-byte limm
   value, is encoded as 'middle-endian' for a little-endian target.  This
   function is used for regular 4, 6, and 8 byte instructions as well.  */

static void
md_number_to_chars_midend (char *buf, unsigned long long val, int n)
{
  if (buf == NULL || n <= 0) {
    return;
  }

  if (n == 2) {
    md_number_to_chars (buf, val, n);
    return;
  }

  if (n == 4) {
    md_number_to_chars (buf, (val >> 16) & 0xffff, 2);
    md_number_to_chars (buf + 2, val & 0xffff, 2);
    return;
  }

  if (n == 6) {
    md_number_to_chars (buf, (val >> 32) & 0xffff, 2);
    md_number_to_chars_midend (buf + 2, val & 0xffffffff, 4);
    return;
  }

  if (n == 8) {
    md_number_to_chars_midend (buf, val >> 32, 4);
    md_number_to_chars_midend (buf + 4, val & 0xffffffff, 4);
    return;
  }
}

/* Check if a feature is allowed for a specific CPU.  */

static void
arc_check_feature (void)
{
  unsigned i;

  if (selected_cpu.features == 0 || selected_cpu.name == NULL)
    return;

  for (i = 0; i < ARRAY_SIZE (feature_list); i++)
    {
      if ((selected_cpu.features & feature_list[i].feature) != 0 &&
          (selected_cpu.flags & feature_list[i].cpus) == 0)
        {
          as_bad (_("invalid %s option for %s cpu"), 
                  feature_list[i].name,
                  selected_cpu.name);
        }
    }

  for (i = 0; i < ARRAY_SIZE (conflict_list); i++)
    {
      if ((selected_cpu.features & conflict_list[i]) == conflict_list[i])
        {
          as_bad(_("conflicting ISA extension attributes."));
        }
    }
}

/* Select an appropriate entry from CPU_TYPES based on ARG and initialise
   the relevant static global variables.  Parameter SEL describes where
   this selection originated from.  */

static void
arc_select_cpu (const char *arg, enum mach_selection_type sel)
{
  int i;
  static struct cpu_type old_cpu = { 0, 0, 0, E_ARC_OSABI_CURRENT, 0 };

  gas_assert (sel != MACH_SELECTION_FROM_DEFAULT
              || mach_selection_mode == MACH_SELECTION_NONE);

  if ((mach_selection_mode == MACH_SELECTION_FROM_CPU_DIRECTIVE)
      && (sel == MACH_SELECTION_FROM_CPU_DIRECTIVE))
    {
      as_bad (_("Multiple .cpu directives found"));
      return;
    }

  for (i = 0; cpu_types[i].name; ++i)
    {
      if (strcasecmp (cpu_types[i].name, arg) == 0)
        break;
    }

  if (!cpu_types[i].name)
    as_fatal (_("unknown architecture: %s\n"), arg);

  if (mach_selection_mode == MACH_SELECTION_FROM_COMMAND_LINE)
    {
      gas_assert (sel == MACH_SELECTION_FROM_COMMAND_LINE
                  || sel == MACH_SELECTION_FROM_CPU_DIRECTIVE);
      if (sel == MACH_SELECTION_FROM_CPU_DIRECTIVE
          && selected_cpu.mach != cpu_types[i].mach)
        {
          as_warn (_("Command-line value overrides \".cpu\" directive"));
        }
      return;
    }

  selected_cpu.flags = cpu_types[i].flags;
  selected_cpu.name = cpu_types[i].name;
  selected_cpu.features = cpu_types[i].features | cl_features;
  selected_cpu.mach = cpu_types[i].mach;
  selected_cpu.eflags = ((selected_cpu.eflags & ~EF_ARC_MACH_MSK)
                         | cpu_types[i].eflags);

  arc_check_feature ();

  if (mach_selection_mode != MACH_SELECTION_NONE
      && (old_cpu.mach != selected_cpu.mach))
    {
      bfd_find_target (arc_target_format, stdoutput);
      if (! bfd_set_arch_mach (stdoutput, bfd_arch_arc, selected_cpu.mach))
        as_warn (_("Could not set architecture and machine"));
    }

  mach_selection_mode = sel;
  old_cpu = selected_cpu;
}

/* Here ends all the ARCompact extension instruction assembling
   stuff.  */

static void
arc_extra_reloc (int r_type)
{
  char *sym_name;
  char c;
  symbolS *sym;
  symbolS *lab = NULL;
  fixS *fixP;

  if (*input_line_pointer == '@')
    input_line_pointer++;
  
  c = get_symbol_name (&sym_name);
  sym = symbol_find_or_make (sym_name);
  restore_line_pointer (c);
  
  if (c == ',' && r_type == BFD_RELOC_ARC_TLS_GD_LD)
    {
      char *lab_name;
      
      ++input_line_pointer;
      c = get_symbol_name (&lab_name);
      lab = symbol_find_or_make (lab_name);
      restore_line_pointer (c);
    }

  fixP = fix_new (frag_now,
                  frag_now_fix (),
                  0,
                  sym,
                  0,
                  false,
                  r_type);
  
  if (fixP != NULL)
    fixP->fx_subsy = lab;
}

static symbolS *
arc_lcomm_internal (int ignore ATTRIBUTE_UNUSED,
		    symbolS *symbolP, addressT size)
{
  addressT align;
  
  if (symbolP == NULL)
    return NULL;
    
  SKIP_WHITESPACE ();

  if (*input_line_pointer == ',')
    {
      align = parse_align (1);
      if (align == (addressT) -1)
	return NULL;
    }
  else
    {
      align = calculate_alignment_from_size (size);
    }

  bss_alloc (symbolP, size, align);
  S_CLEAR_EXTERNAL (symbolP);

  return symbolP;
}

static addressT
calculate_alignment_from_size (addressT size)
{
  if (size >= 8)
    return 3;
  if (size >= 4)
    return 2;
  if (size >= 2)
    return 1;
  return 0;
}

static void
arc_lcomm (int ignore)
{
  symbolS *symbolP = s_comm_internal (ignore, arc_lcomm_internal);

  if (symbolP != NULL)
    {
      asymbol *bfdsym = symbol_get_bfdsym (symbolP);
      if (bfdsym != NULL)
        bfdsym->flags |= BSF_OBJECT;
    }
}

/* Select the cpu we're assembling for.  */

static void
arc_option (int ignore ATTRIBUTE_UNUSED)
{
  char c;
  char *cpu;
  const char *cpu_name;

  c = get_symbol_name (&cpu);
  if (!cpu) {
    restore_line_pointer (c);
    return;
  }

  cpu_name = map_cpu_name(cpu);
  arc_select_cpu (cpu_name, MACH_SELECTION_FROM_CPU_DIRECTIVE);

  restore_line_pointer (c);
  demand_empty_rest_of_line ();
}

static const char *
map_cpu_name(const char *cpu)
{
  static const struct {
    const char *input;
    const char *output;
  } cpu_map[] = {
    {"ARC600", "arc600"},
    {"ARC601", "arc600"},
    {"A6", "arc600"},
    {"ARC700", "arc700"},
    {"A7", "arc700"},
    {"EM", "arcem"},
    {"HS", "archs"},
    {"NPS400", "nps400"}
  };

  size_t i;
  for (i = 0; i < sizeof(cpu_map) / sizeof(cpu_map[0]); i++) {
    if (strcmp(cpu_map[i].input, cpu) == 0) {
      return cpu_map[i].output;
    }
  }
  
  return cpu;
}

/* Smartly print an expression.  */

static void
debug_exp (expressionS *t)
{
  const char *name;
  const char *namemd;

  if (!t)
    return;

  pr_debug ("debug_exp: ");

  switch (t->X_op)
    {
    case O_illegal:		name = "O_illegal";		break;
    case O_absent:		name = "O_absent";		break;
    case O_constant:		name = "O_constant";		break;
    case O_symbol:		name = "O_symbol";		break;
    case O_symbol_rva:		name = "O_symbol_rva";		break;
    case O_register:		name = "O_register";		break;
    case O_big:			name = "O_big";			break;
    case O_uminus:		name = "O_uminus";		break;
    case O_bit_not:		name = "O_bit_not";		break;
    case O_logical_not:		name = "O_logical_not";		break;
    case O_multiply:		name = "O_multiply";		break;
    case O_divide:		name = "O_divide";		break;
    case O_modulus:		name = "O_modulus";		break;
    case O_left_shift:		name = "O_left_shift";		break;
    case O_right_shift:		name = "O_right_shift";		break;
    case O_bit_inclusive_or:	name = "O_bit_inclusive_or";	break;
    case O_bit_or_not:		name = "O_bit_or_not";		break;
    case O_bit_exclusive_or:	name = "O_bit_exclusive_or";	break;
    case O_bit_and:		name = "O_bit_and";		break;
    case O_add:			name = "O_add";			break;
    case O_subtract:		name = "O_subtract";		break;
    case O_eq:			name = "O_eq";			break;
    case O_ne:			name = "O_ne";			break;
    case O_lt:			name = "O_lt";			break;
    case O_le:			name = "O_le";			break;
    case O_ge:			name = "O_ge";			break;
    case O_gt:			name = "O_gt";			break;
    case O_logical_and:		name = "O_logical_and";		break;
    case O_logical_or:		name = "O_logical_or";		break;
    case O_index:		name = "O_index";		break;
    case O_bracket:		name = "O_bracket";		break;
    case O_colon:		name = "O_colon";		break;
    case O_addrtype:		name = "O_addrtype";		break;
    default:			name = "unknown";		break;
    }

  switch (t->X_md)
    {
    case O_gotoff:		namemd = "O_gotoff";		break;
    case O_gotpc:		namemd = "O_gotpc";		break;
    case O_plt:			namemd = "O_plt";		break;
    case O_sda:			namemd = "O_sda";		break;
    case O_pcl:			namemd = "O_pcl";		break;
    case O_tlsgd:		namemd = "O_tlsgd";		break;
    case O_tlsie:		namemd = "O_tlsie";		break;
    case O_tpoff9:		namemd = "O_tpoff9";		break;
    case O_tpoff:		namemd = "O_tpoff";		break;
    case O_dtpoff9:		namemd = "O_dtpoff9";		break;
    case O_dtpoff:		namemd = "O_dtpoff";		break;
    default:			namemd = "unknown";		break;
    }

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
  const struct arc_reloc_op_tag *r;
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

  r = NULL;
  for (int i = 0; i < arc_num_reloc_op; i++)
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
      if (resultP->X_op_symbol != NULL || resultP->X_op != O_symbol)
        {
          as_bad (_("Unable to parse TLS base: %s"), input_line_pointer);
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
          as_bad (_("Bad expression: @%s + %s."), r->name, input_line_pointer);
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

  if (str == NULL || tok == NULL || ntok <= 0)
    return -1;

  memset (tok, 0, sizeof (*tok) * ntok);

  old_input_line_pointer = input_line_pointer;
  input_line_pointer = str;

  while (*input_line_pointer)
    {
      SKIP_WHITESPACE ();
      
      if (*input_line_pointer == '\0')
        break;

      if (*input_line_pointer == ',')
        {
          input_line_pointer++;
          if (saw_comma || !saw_arg)
            {
              report_tokenize_error(brk_lvl, saw_comma, saw_arg);
              input_line_pointer = old_input_line_pointer;
              return -1;
            }
          saw_comma = true;
          continue;
        }

      if (*input_line_pointer == '}' || *input_line_pointer == ']')
        {
          ++input_line_pointer;
          --brk_lvl;
          if (!saw_arg || num_args >= ntok)
            {
              report_tokenize_error(brk_lvl, saw_comma, saw_arg);
              input_line_pointer = old_input_line_pointer;
              return -1;
            }
          tok->X_op = O_bracket;
          ++tok;
          ++num_args;
          continue;
        }

      if (*input_line_pointer == '{' || *input_line_pointer == '[')
        {
          input_line_pointer++;
          if (brk_lvl || num_args >= ntok)
            {
              report_tokenize_error(brk_lvl, saw_comma, saw_arg);
              input_line_pointer = old_input_line_pointer;
              return -1;
            }
          ++brk_lvl;
          tok->X_op = O_bracket;
          ++tok;
          ++num_args;
          continue;
        }

      if (*input_line_pointer == ':')
        {
          input_line_pointer++;
          if (!saw_arg || num_args >= ntok)
            {
              report_tokenize_error(brk_lvl, saw_comma, saw_arg);
              input_line_pointer = old_input_line_pointer;
              return -1;
            }
          tok->X_op = O_colon;
          saw_arg = false;
          ++tok;
          ++num_args;
          continue;
        }

      if (*input_line_pointer == '@')
        {
          if ((saw_arg && !saw_comma) || num_args >= ntok)
            {
              report_tokenize_error(brk_lvl, saw_comma, saw_arg);
              input_line_pointer = old_input_line_pointer;
              return -1;
            }

          input_line_pointer++;
          tok->X_op = O_symbol;
          tok->X_md = O_absent;
          expression (tok);

          if (*input_line_pointer == '@')
            parse_reloc_symbol (tok);

          debug_exp (tok);

          if (tok->X_op == O_illegal || tok->X_op == O_absent)
            {
              report_tokenize_error(brk_lvl, saw_comma, saw_arg);
              input_line_pointer = old_input_line_pointer;
              return -1;
            }

          saw_comma = false;
          saw_arg = true;
          tok++;
          num_args++;
          continue;
        }

      if (*input_line_pointer == '%')
        ++input_line_pointer;

      if ((saw_arg && !saw_comma) || num_args >= ntok)
        {
          report_tokenize_error(brk_lvl, saw_comma, saw_arg);
          input_line_pointer = old_input_line_pointer;
          return -1;
        }

      tok->X_op = O_absent;
      tok->X_md = O_absent;
      expression (tok);

      if (*input_line_pointer == '@')
        parse_reloc_symbol (tok);
      else
        resolve_register (tok);

      debug_exp (tok);

      if (tok->X_op == O_illegal || tok->X_op == O_absent)
        {
          report_tokenize_error(brk_lvl, saw_comma, saw_arg);
          input_line_pointer = old_input_line_pointer;
          return -1;
        }

      saw_comma = false;
      saw_arg = true;
      tok++;
      num_args++;
    }

  if (saw_comma || brk_lvl)
    {
      report_tokenize_error(brk_lvl, saw_comma, saw_arg);
      input_line_pointer = old_input_line_pointer;
      return -1;
    }

  input_line_pointer = old_input_line_pointer;
  return num_args;
}

static void
report_tokenize_error(int brk_lvl, bool saw_comma, bool saw_arg)
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

/* Parse the flags to a structure.  */

static int
tokenize_flags (const char *str,
		struct arc_flags flags[],
		int nflg)
{
  char *old_input_line_pointer;
  bool saw_flg = false;
  bool saw_dot = false;
  int num_flags  = 0;
  size_t flgnamelen;

  if (!str || !flags || nflg <= 0)
    return -1;

  memset (flags, 0, sizeof (*flags) * nflg);

  old_input_line_pointer = input_line_pointer;
  input_line_pointer = (char *) str;

  while (*input_line_pointer)
    {
      if (*input_line_pointer == '.')
	{
	  input_line_pointer++;
	  if (saw_dot)
	    {
	      as_bad (_("extra dot"));
	      input_line_pointer = old_input_line_pointer;
	      return -1;
	    }
	  saw_dot = true;
	  saw_flg = false;
	  continue;
	}

      if (is_end_of_stmt (*input_line_pointer)
	  || is_whitespace (*input_line_pointer))
	break;

      if (saw_flg && !saw_dot)
	{
	  as_bad (_("failed to parse flags"));
	  input_line_pointer = old_input_line_pointer;
	  return -1;
	}

      if (num_flags >= nflg)
	{
	  as_bad (_("failed to parse flags"));
	  input_line_pointer = old_input_line_pointer;
	  return -1;
	}

      flgnamelen = strspn (input_line_pointer,
			   "abcdefghijklmnopqrstuvwxyz0123456789");
      if (flgnamelen > MAX_FLAG_NAME_LENGTH)
	{
	  as_bad (_("unrecognized flag"));
	  input_line_pointer = old_input_line_pointer;
	  return -1;
	}

      memcpy (flags[num_flags].name, input_line_pointer, flgnamelen);
      flags[num_flags].name[flgnamelen] = '\0';

      input_line_pointer += flgnamelen;
      saw_dot = false;
      saw_flg = true;
      num_flags++;
    }

  input_line_pointer = old_input_line_pointer;
  return num_flags;
}

/* Apply the fixups in order.  */

static void
apply_fixups (struct arc_insn *insn, fragS *fragP, int fix)
{
  if (!insn || !fragP) {
    return;
  }

  for (int i = 0; i < insn->nfixups; i++)
    {
      struct arc_fixup *fixup = &insn->fixups[i];
      if (!fixup) {
        continue;
      }

      if (fixup->reloc == 0) {
        as_fatal (_("Unhandled reloc type"));
      }

      int size = ((insn->len == 2) && !fixup->islong) ? 2 : 4;
      int offset = fixup->islong ? insn->len : 0;
      int pcrel;

      if ((int) fixup->reloc < 0)
        {
          pcrel = fixup->pcrel;
        }
      else
        {
          reloc_howto_type *reloc_howto =
            bfd_reloc_type_lookup (stdoutput, fixup->reloc);
          gas_assert (reloc_howto);
          pcrel = reloc_howto->pc_relative;
        }

      pr_debug ("%s:%d: apply_fixups: new %s fixup (PCrel:%s) of size %d @ \
offset %d + %d\n",
                fragP->fr_file, fragP->fr_line,
                (fixup->reloc < 0) ? "Internal" :
                bfd_get_reloc_code_name (fixup->reloc),
                pcrel ? "Y" : "N",
                size, fix, offset);
      
      fix_new_exp (fragP, fix + offset,
                   size, &fixup->exp, pcrel, fixup->reloc);

      if (LP_INSN (insn->insn))
        {
          gas_assert (fixup->exp.X_add_symbol);
          ARC_SET_FLAG (fixup->exp.X_add_symbol, ARC_FLAG_ZOL);
        }
    }
}

/* Actually output an instruction with its fixup.  */

static void
emit_insn0 (struct arc_insn *insn, char *where, bool relax)
{
  char *f = where;
  size_t total_len;
  
  if (insn == NULL) {
    return;
  }

  pr_debug ("Emit insn : 0x%llx\n", insn->insn);
  pr_debug ("\tLength  : %d\n", insn->len);
  pr_debug ("\tLong imm: 0x%lx\n", insn->limm);

  total_len = insn->len;
  if (insn->has_limm) {
    total_len += 4;
  }
  
  if (!relax) {
    f = frag_more (total_len);
    if (f == NULL) {
      return;
    }
  }

  md_number_to_chars_midend(f, insn->insn, insn->len);

  if (insn->has_limm) {
    md_number_to_chars_midend (f + insn->len, insn->limm, 4);
  }
  
  dwarf2_emit_insn (total_len);

  if (!relax) {
    apply_fixups (insn, frag_now, (f - frag_now->fr_literal));
  }
}

static void
emit_insn1 (struct arc_insn *insn)
{
  symbolS *s = make_expr_symbol (&insn->fixups[0].exp);
  frag_now->tc_frag_data.pcrel = insn->fixups[0].pcrel;

  if (frag_room () < FRAG_MAX_GROWTH)
    {
      struct arc_relax_type relax_info_copy;
      relax_substateT subtype = frag_now->fr_subtype;

      memcpy (&relax_info_copy, &frag_now->tc_frag_data,
	      sizeof (struct arc_relax_type));

      frag_wane (frag_now);
      frag_grow (FRAG_MAX_GROWTH);

      memcpy (&frag_now->tc_frag_data, &relax_info_copy,
	      sizeof (struct arc_relax_type));

      frag_var (rs_machine_dependent, FRAG_MAX_GROWTH, 0,
		subtype, s, 0, 0);
    }
  else
    {
      frag_var (rs_machine_dependent, FRAG_MAX_GROWTH, 0,
	        frag_now->fr_subtype, s, 0, 0);
    }
}

static void
emit_insn (struct arc_insn *insn)
{
  if (!insn)
    return;
    
  if (insn->relax)
    emit_insn1 (insn);
  else
    emit_insn0 (insn, NULL, false);
}

/* Check whether a symbol involves a register.  */

static bool
contains_register (symbolS *sym)
{
  if (!sym)
    return false;

  expressionS *ex = symbol_get_value_expression (sym);
  
  if (ex->X_op != O_register)
    return false;
    
  if (contains_register (ex->X_add_symbol))
    return false;
    
  if (contains_register (ex->X_op_symbol))
    return false;
    
  return true;
}

/* Returns the register number within a symbol.  */

static int
get_register (symbolS *sym)
{
  expressionS *ex;
  
  if (sym == NULL || !contains_register (sym))
    return -1;

  ex = symbol_get_value_expression (sym);
  if (ex == NULL)
    return -1;
    
  return regno (ex->X_add_number);
}

/* Return true if a RELOC is generic.  A generic reloc is PC-rel of a
   simple ME relocation (e.g. RELOC_ARC_32_ME, BFD_RELOC_ARC_PC32.  */

static bool
generic_reloc_p (extended_bfd_reloc_code_real_type reloc)
{
  if (!reloc)
    return false;

  return reloc != BFD_RELOC_ARC_SDA_LDST &&
         reloc != BFD_RELOC_ARC_SDA_LDST1 &&
         reloc != BFD_RELOC_ARC_SDA_LDST2 &&
         reloc != BFD_RELOC_ARC_SDA16_LD &&
         reloc != BFD_RELOC_ARC_SDA16_LD1 &&
         reloc != BFD_RELOC_ARC_SDA16_LD2 &&
         reloc != BFD_RELOC_ARC_SDA16_ST2 &&
         reloc != BFD_RELOC_ARC_SDA32_ME;
}

/* Allocates a tok entry.  */

static int
allocate_tok (expressionS *tok, int ntok, int cidx)
{
  if (ntok > MAX_INSN_ARGS - 2)
    return 0;

  if (cidx > ntok)
    return 0;

  if (cidx == ntok)
  {
    memcpy (&tok[ntok+1], &tok[ntok], sizeof (*tok));
    return 1;
  }

  for (int i = ntok; i > cidx; i--)
  {
    memcpy (&tok[i+1], &tok[i], sizeof (*tok));
  }
  
  return 1;
}

/* Check if an particular ARC feature is enabled.  */

static bool
check_cpu_feature (insn_subclass_t sc)
{
  typedef struct {
    bool (*check_func)(insn_subclass_t);
    unsigned int feature_flag;
  } feature_check_t;

  static const feature_check_t feature_checks[] = {
    { is_code_density_p, CD },
    { is_spfp_p, SPX },
    { is_dpfp_p, DPX },
    { is_fpuda_p, DPA },
    { is_nps400_p, NPS400 }
  };

  for (size_t i = 0; i < sizeof(feature_checks) / sizeof(feature_checks[0]); i++) {
    if (feature_checks[i].check_func(sc) && !(selected_cpu.features & feature_checks[i].feature_flag)) {
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
parse_opcode_flags (const struct arc_opcode *opcode,
                    int nflgs,
                    struct arc_flags *first_pflag)
{
  int remaining_flags = nflgs;
  const unsigned char *flgidx;

  for (int i = 0; i < nflgs; i++)
    first_pflag[i].flgp = NULL;

  for (flgidx = opcode->flags; *flgidx; ++flgidx)
    {
      const struct arc_flag_class *cl_flags = &arc_flag_classes[*flgidx];
      int cl_matches = 0;

      if (cl_flags->flag_class & F_CLASS_IMPLICIT)
        continue;

      if (ext_condcode.arc_ext_condcode
          && (cl_flags->flag_class & F_CLASS_EXTEND))
        {
          cl_matches = process_extension_flags(ext_condcode.arc_ext_condcode,
                                                first_pflag, nflgs, &remaining_flags);
          if (cl_matches < 0)
            return false;
        }

      int matches = process_flag_class(cl_flags, first_pflag, nflgs, &remaining_flags);
      if (matches < 0)
        return false;
      cl_matches += matches;

      if ((cl_flags->flag_class & F_CLASS_REQUIRED) && cl_matches == 0)
        return false;
      if ((cl_flags->flag_class & F_CLASS_OPTIONAL) && cl_matches > 1)
        return false;
    }

  return remaining_flags == 0;
}

static int
process_extension_flags(struct arc_flag_operand *pf,
                         struct arc_flags *first_pflag,
                         int nflgs,
                         int *remaining_flags)
{
  int matches = 0;
  
  while (pf->name)
    {
      for (int i = 0; i < nflgs; i++)
        {
          if (!strcmp(pf->name, first_pflag[i].name))
            {
              if (first_pflag[i].flgp != NULL)
                return -1;
              first_pflag[i].flgp = pf;
              matches++;
              (*remaining_flags)--;
              break;
            }
        }
      pf++;
    }
  return matches;
}

static int
process_flag_class(const struct arc_flag_class *cl_flags,
                   struct arc_flags *first_pflag,
                   int nflgs,
                   int *remaining_flags)
{
  const unsigned *flgopridx;
  int matches = 0;

  for (flgopridx = cl_flags->flags; *flgopridx; ++flgopridx)
    {
      const struct arc_flag_operand *flg_operand = &arc_flag_operands[*flgopridx];
      
      for (int i = 0; i < nflgs; i++)
        {
          if (!strcmp(flg_operand->name, first_pflag[i].name))
            {
              if (first_pflag[i].flgp != NULL)
                return -1;
              first_pflag[i].flgp = flg_operand;
              matches++;
              (*remaining_flags)--;
              break;
            }
        }
    }
  return matches;
}


/* Search forward through all variants of an opcode looking for a
   syntax match.  */

static const struct arc_opcode *
find_opcode_match (const struct arc_opcode_hash_entry *entry,
		   expressionS *tok,
		   int *pntok,
		   struct arc_flags *first_pflag,
		   int nflgs,
		   int *pcpumatch,
		   const char **errmsg)
{
  const struct arc_opcode *opcode;
  struct arc_opcode_hash_entry_iterator iter;
  int ntok = *pntok;
  int got_cpu_match = 0;
  expressionS bktok[MAX_INSN_ARGS];
  int bkntok, maxerridx = 0;
  expressionS emptyE;
  const char *tmpmsg = NULL;

  arc_opcode_hash_entry_iterator_init (&iter);
  memset (&emptyE, 0, sizeof (emptyE));
  memcpy (bktok, tok, MAX_INSN_ARGS * sizeof (*tok));
  bkntok = ntok;

  for (opcode = arc_opcode_hash_entry_iterator_next (entry, &iter);
       opcode != NULL;
       opcode = arc_opcode_hash_entry_iterator_next (entry, &iter))
    {
      const unsigned char *opidx;
      int tokidx = 0;
      const expressionS *t = &emptyE;

      pr_debug ("%s:%d: find_opcode_match: trying opcode 0x%08llX ",
		frag_now->fr_file, frag_now->fr_line, opcode->opcode);

      if (!(opcode->cpu & selected_cpu.flags))
	goto match_failed;

      if (!check_cpu_feature (opcode->subclass))
	goto match_failed;

      got_cpu_match = 1;
      pr_debug ("cpu ");

      for (opidx = opcode->operands; *opidx; ++opidx)
	{
	  const struct arc_operand *operand = &arc_operands[*opidx];

	  if (ARC_OPERAND_IS_FAKE (operand))
	    continue;

	  if (tokidx >= ntok)
	    goto match_failed;

	  if (!process_operand_match(operand, tok, &tokidx, &ntok, &t, &tmpmsg))
	    goto match_failed;

	  ++tokidx;
	}
      pr_debug ("opr ");

      if (!parse_opcode_flags (opcode, nflgs, first_pflag))
	{
	  tmpmsg = _("flag mismatch");
	  goto match_failed;
	}

      pr_debug ("flg");
      if (tokidx == ntok)
	{
	  *pntok = ntok;
	  pr_debug ("\n");
	  return opcode;
	}
      tmpmsg = _("too many arguments");

    match_failed:;
      pr_debug ("\n");
      memcpy (tok, bktok, MAX_INSN_ARGS * sizeof (*tok));
      ntok = bkntok;
      if (tokidx >= maxerridx && tmpmsg)
	{
	  maxerridx = tokidx;
	  *errmsg = tmpmsg;
	}
    }

  if (*pcpumatch)
    *pcpumatch = got_cpu_match;

  return NULL;
}

static int
process_operand_match(const struct arc_operand *operand,
		      expressionS *tok,
		      int *tokidx,
		      int *ntok,
		      const expressionS **t,
		      const char **tmpmsg)
{
  switch (operand->flags & ARC_OPERAND_TYPECHECK_MASK)
    {
    case ARC_OPERAND_ADDRTYPE:
      return process_address_operand(operand, tok, *tokidx, tmpmsg);

    case ARC_OPERAND_IR:
      return process_register_operand(operand, tok, tokidx, ntok, t, tmpmsg);

    case ARC_OPERAND_BRAKET:
      return tok[*tokidx].X_op == O_bracket;

    case ARC_OPERAND_COLON:
      return tok[*tokidx].X_op == O_colon;

    case ARC_OPERAND_LIMM:
    case ARC_OPERAND_SIGNED:
    case ARC_OPERAND_UNSIGNED:
      return process_immediate_operand(operand, tok, tokidx, ntok, t, tmpmsg);

    default:
      abort ();
    }
  return 0;
}

static int
process_address_operand(const struct arc_operand *operand,
			expressionS *tok,
			int tokidx,
			const char **tmpmsg)
{
  *tmpmsg = NULL;
  
  if (tok[tokidx].X_op != O_addrtype)
    return 0;

  gas_assert (operand->insert != NULL);
  (*operand->insert) (0, tok[tokidx].X_add_number, tmpmsg);
  
  return *tmpmsg == NULL;
}

static int
process_register_operand(const struct arc_operand *operand,
			 expressionS *tok,
			 int *tokidx,
			 int *ntok,
			 const expressionS **t,
			 const char **tmpmsg)
{
  if ((tok[*tokidx].X_op != O_register || !is_ir_num (tok[*tokidx].X_add_number))
      && !(operand->flags & ARC_OPERAND_IGNORE))
    return 0;

  if (operand->flags & ARC_OPERAND_DUPLICATE)
    {
      if ((*t)->X_op != O_register || !is_ir_num ((*t)->X_add_number)
	  || (regno ((*t)->X_add_number) != regno (tok[*tokidx].X_add_number)))
	return 0;
    }

  if (operand->insert)
    {
      *tmpmsg = NULL;
      (*operand->insert)(0, regno (tok[*tokidx].X_add_number), tmpmsg);
      if (*tmpmsg)
	{
	  if (operand->flags & ARC_OPERAND_IGNORE)
	    {
	      if (!allocate_tok (tok, *ntok - 1, *tokidx))
		return 0;
	      tok[*tokidx].X_op = O_absent;
	      ++(*ntok);
	    }
	  else
	    return 0;
	}
    }

  *t = &tok[*tokidx];
  return 1;
}

static int
process_immediate_operand(const struct arc_operand *operand,
			  expressionS *tok,
			  int *tokidx,
			  int *ntok,
			  const expressionS **t,
			  const char **tmpmsg)
{
  switch (tok[*tokidx].X_op)
    {
    case O_illegal:
    case O_absent:
    case O_register:
      return 0;

    case O_bracket:
      if (!(operand->flags & ARC_OPERAND_IGNORE))
	return 0;
      if (!allocate_tok (tok, *ntok - 1, *tokidx))
	return 0;
      tok[*tokidx].X_op = O_absent;
      ++(*ntok);
      break;

    case O_symbol:
      if (!process_symbol_operand(operand, tok, *tokidx))
	goto de_fault;
      
    case O_constant:
      if (!validate_constant_operand(operand, tok[*tokidx].X_add_number, tmpmsg))
	return 0;
      break;

    case O_subtract:
      if (!process_register_range(operand, tok, *tokidx, tmpmsg))
	goto de_fault;
      break;

    default:
    de_fault:
      if (!process_relocation_operand(operand, tok, *tokidx))
	return 0;
      break;
    }

  if (operand->flags & ARC_OPERAND_DUPLICATE)
    {
      if ((*t)->X_op == O_illegal || (*t)->X_op == O_absent
	  || (*t)->X_op == O_register
	  || ((*t)->X_add_number != tok[*tokidx].X_add_number))
	{
	  *tmpmsg = _("operand is not duplicate of the previous one");
	  return 0;
	}
    }
  
  *t = &tok[*tokidx];
  return 1;
}

static int
process_symbol_operand(const struct arc_operand *operand,
		       expressionS *tok,
		       int tokidx)
{
  const char *p;
  char *tmpp, *pp;
  const struct arc_aux_reg *auxr;

  if (opcode->insn_class != AUXREG)
    return 0;
    
  p = S_GET_NAME (tok[tokidx].X_add_symbol);
  tmpp = strdup (p);
  if (!tmpp)
    return 0;
    
  for (pp = tmpp; *pp; ++pp) 
    *pp = TOLOWER (*pp);

  auxr = str_hash_find (arc_aux_hash, tmpp);
  if (auxr)
    {
      tok[tokidx].X_op = O_constant;
      tok[tokidx].X_add_number = auxr->address;
      ARC_SET_FLAG (tok[tokidx].X_add_symbol, ARC_FLAG_AUX);
    }
  free (tmpp);

  return tok[tokidx].X_op == O_constant;
}

static int
validate_constant_operand(const struct arc_operand *operand,
			  offsetT val,
			  const char **tmpmsg)
{
  if (operand->bits != 32 && !(operand->flags & ARC_OPERAND_NCHK))
    {
      offsetT min, max;

      if (operand->flags & ARC_OPERAND_SIGNED)
	{
	  max = (1 << (operand->bits - 1)) - 1;
	  min = -(1 << (operand->bits - 1));
	}
      else
	{
	  max = (1 << operand->bits) - 1;
	  min = 0;
	}

      if (val < min || val > max)
	{
	  *tmpmsg = _("immediate is out of bounds");
	  return 0;
	}

      if ((operand->flags & ARC_OPERAND_ALIGNED32) && (val & 0x03))
	{
	  *tmpmsg = _("immediate is not 32bit aligned");
	  return 0;
	}

      if ((operand->flags & ARC_OPERAND_ALIGNED16) && (val & 0x01))
	{
	  *tmpmsg = _("immediate is not 16bit aligned");
	  return 0;
	}
    }
  else if (operand->flags & ARC_OPERAND_NCHK)
    {
      if (operand->insert)
	{
	  *tmpmsg = NULL;
	  (*operand->insert)(0, val, tmpmsg);
	  if (*tmpmsg)
	    return 0;
	}
      else if (!(operand->flags & ARC_OPERAND_IGNORE))
	return 0;
    }
  
  return 1;
}

static int
process_register_range(const struct arc_operand *operand,
		       expressionS *tok,
		       int tokidx,
		       const char **tmpmsg)
{
  int regs;
  
  if (tok[tokidx].X_add_number != 0)
    return 0;
    
  if (!contains_register (tok[tokidx].X_add_symbol))
    return 0;
    
  if (!contains_register (tok[tokidx].X_op_symbol))
    return 0;

  regs = get_register (tok[tokidx].X_add_symbol);
  regs <<= 16;
  regs |= get_register (tok[tokidx].X_op_symbol);
  
  if (operand->insert)
    {
      *tmpmsg = NULL;
      (*operand->insert)(0, regs, tmpmsg);
      if (*tmpmsg)
	return 0;
    }
  else
    return 0;
    
  return 1;
}

static int
process_relocation_operand(const struct arc_operand *operand,
			   expressionS *tok,
			   int tokidx)
{
  if (operand->default_reloc == 0)
    return 0;

  switch (tok[tokidx].X_md)
    {
    case O_gotoff:
    case O_gotpc:
    case O_pcl:
    case O_tpoff:
    case O_dtpoff:
    case O_tlsgd:
    case O_tlsie:
      if (!(operand->flags & ARC_OPERAND_LIMM))
	return 0;
      
    case O_absent:
      if (!generic_reloc_p (operand->default_reloc))
	return 0;
      break;
      
    default:
      break;
    }
  
  return 1;
}

/* Swap operand tokens.  */

static void
swap_operand (expressionS *operand_array,
	      unsigned source,
	      unsigned destination)
{
  expressionS temp;

  if (source == destination)
    return;

  temp = operand_array[destination];
  operand_array[destination] = operand_array[source];
  operand_array[source] = temp;
}

/* Check if *op matches *tok type.
   Returns FALSE if they don't match, TRUE if they match.  */

static bool
pseudo_operand_match (const expressionS *tok,
		      const struct arc_operand_operation *op)
{
  const struct arc_operand *operand_real = &arc_operands[op->operand_idx];

  switch (tok->X_op)
    {
    case O_constant:
      if (operand_real->bits == 32 && (operand_real->flags & ARC_OPERAND_LIMM))
	return true;
      
      if (operand_real->flags & ARC_OPERAND_IR)
	return false;
      
      offsetT val = tok->X_add_number + op->count;
      offsetT max, min;
      
      if (operand_real->flags & ARC_OPERAND_SIGNED)
	{
	  max = (1 << (operand_real->bits - 1)) - 1;
	  min = -(1 << (operand_real->bits - 1));
	}
      else
	{
	  max = (1 << operand_real->bits) - 1;
	  min = 0;
	}
      return (min <= val && val <= max);

    case O_symbol:
      return (operand_real->flags & ARC_OPERAND_LIMM) ||
	     ((operand_real->flags & ARC_OPERAND_SIGNED) && operand_real->bits == 9);

    case O_register:
      return (operand_real->flags & ARC_OPERAND_IR) != 0;

    case O_bracket:
      return (operand_real->flags & ARC_OPERAND_BRAKET) != 0;

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
  if (opname == NULL || tok == NULL || ntok < 0) {
    return NULL;
  }

  for (unsigned int i = 0; i < arc_num_pseudo_insn; ++i)
    {
      const struct arc_pseudo_insn *pseudo_insn = &arc_pseudo_insns[i];
      
      if (pseudo_insn->mnemonic_p == NULL) {
        continue;
      }
      
      if (strcmp (pseudo_insn->mnemonic_p, opname) != 0) {
        continue;
      }

      if (pseudo_insn->operand == NULL) {
        continue;
      }

      const struct arc_operand_operation *op = pseudo_insn->operand;
      int j = 0;
      
      while (j < ntok && pseudo_operand_match (&tok[j], &op[j])) {
        j++;
      }

      if (j == ntok) {
        return pseudo_insn;
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
  const struct arc_pseudo_insn *pseudo_insn = NULL;
  char construct_operand[MAX_CONSTR_STR];

  if (opname == NULL || ntok == NULL || tok == NULL || nflgs == NULL || pflags == NULL)
    return NULL;

  pseudo_insn = find_pseudo_insn (opname, *ntok, tok);
  if (pseudo_insn == NULL)
    return NULL;

  if (pseudo_insn->flag_r != NULL && *nflgs < MAX_INSN_FLGS)
    {
      int flags_added = tokenize_flags (pseudo_insn->flag_r, &pflags[*nflgs],
					 MAX_INSN_FLGS - *nflgs);
      *nflgs += flags_added;
    }

  for (unsigned i = 0; i < pseudo_insn->operand_cnt; ++i)
    {
      const struct arc_operand_operation *operand_pseudo = &pseudo_insn->operand[i];
      const struct arc_operand *operand_real = &arc_operands[operand_pseudo->operand_idx];

      if ((operand_real->flags & ARC_OPERAND_BRAKET) && !operand_pseudo->needs_insert)
	continue;

      if (operand_pseudo->needs_insert)
	{
	  if (operand_real->flags & ARC_OPERAND_BRAKET)
	    {
	      tok[i].X_op = O_bracket;
	      (*ntok)++;
	    }
	  else
	    {
	      const char *format = (operand_real->flags & ARC_OPERAND_IR) ? "r%d" : "%d";
	      int ret = snprintf (construct_operand, MAX_CONSTR_STR, format,
				  operand_pseudo->count);
	      if (ret > 0 && ret < MAX_CONSTR_STR)
		{
		  tokenize_arguments (construct_operand, &tok[i], 1);
		  (*ntok)++;
		}
	    }
	}
      else if (operand_pseudo->count && tok[i].X_op == O_constant)
	{
	  tok[i].X_add_number += operand_pseudo->count;
	}
    }

  for (unsigned i = 0; i < pseudo_insn->operand_cnt; ++i)
    {
      const struct arc_operand_operation *operand_pseudo = &pseudo_insn->operand[i];
      
      if (operand_pseudo->swap_operand_idx != i)
	{
	  swap_operand (tok, i, operand_pseudo->swap_operand_idx);
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
  if (opname == NULL || nflgs == NULL || pflags == NULL)
    return NULL;

  for (unsigned int i = 0; i < arc_num_flag_special; i++)
    {
      const struct arc_flag_special *special_case = &arc_flag_special_cases[i];
      if (special_case == NULL || special_case->name == NULL)
        continue;

      size_t oplen = strlen (special_case->name);
      if (strncmp (opname, special_case->name, oplen) != 0)
        continue;

      for (unsigned int flag_arr_idx = 0; ; flag_arr_idx++)
        {
          unsigned int flag_idx = special_case->flags[flag_arr_idx];
          if (flag_idx == 0)
            break;

          const char *flagnm = arc_flag_operands[flag_idx].name;
          if (flagnm == NULL)
            break;

          if (strcmp (opname + oplen, flagnm) == 0)
            {
              if (*nflgs >= MAX_INSN_FLGS)
                return NULL;

              const struct arc_opcode_hash_entry *entry = arc_find_opcode (special_case->name);
              if (entry == NULL)
                return NULL;

              size_t flaglen = strlen (flagnm);
              if (flaglen >= sizeof(pflags[*nflgs].name))
                return NULL;

              memcpy (pflags[*nflgs].name, flagnm, flaglen);
              pflags[*nflgs].name[flaglen] = '\0';
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
  const struct arc_opcode_hash_entry *entry = NULL;

  if (opname == NULL || nflgs == NULL || pflags == NULL || tok == NULL || ntok == NULL)
    return NULL;

  entry = find_special_case_pseudo (opname, ntok, tok, nflgs, pflags);

  if (entry == NULL)
    entry = find_special_case_flag (opname, nflgs, pflags);

  return entry;
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
    { MPY1E, 1 }, 
    { MPY6E, 6 }, 
    { MPY7E, 7 }, 
    { MPY8E, 8 },
    { MPY9E, 9 }
  };

  if (opcode == NULL || (tok == NULL && ntok > 0)) {
    return;
  }

  for (unsigned i = 0; i < ARRAY_SIZE (feature_list); i++) {
    if (opcode->subclass == feature_list[i].feature) {
      selected_cpu.features |= feature_list[i].feature;
    }
  }

  for (unsigned i = 0; i < ARRAY_SIZE (mpy_list); i++) {
    if (opcode->subclass == mpy_list[i].feature) {
      mpy_option = mpy_list[i].encoding;
      break;
    }
  }

  for (int i = 0; i < ntok; i++) {
    switch (tok[i].X_md) {
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

    if (tok[i].X_op == O_register) {
      unsigned reg_num = tok[i].X_add_number;
      if ((reg_num >= 4 && reg_num <= 9) || 
          (reg_num >= 16 && reg_num <= 25)) {
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
  const struct arc_opcode_hash_entry *entry;
  const struct arc_opcode *opcode;
  struct arc_insn insn;
  int cpumatch = 1;
  const char *errmsg = NULL;

  if (opname == NULL || tok == NULL || pflags == NULL)
    {
      as_bad (_("invalid parameters for assembly"));
      return;
    }

  entry = arc_find_opcode (opname);
  if (entry == NULL)
    entry = find_special_case (opname, &nflgs, pflags, tok, &ntok);

  if (entry == NULL)
    {
      as_bad (_("unknown opcode '%s'"), opname);
      return;
    }

  pr_debug ("%s:%d: assemble_tokens: %s\n",
	    frag_now->fr_file, frag_now->fr_line, opname);

  opcode = find_opcode_match (entry, tok, &ntok, pflags,
			      nflgs, &cpumatch, &errmsg);
  
  if (opcode == NULL)
    {
      if (!cpumatch)
	as_bad (_("opcode '%s' not supported for target %s"), opname,
		selected_cpu.name);
      else if (errmsg != NULL)
	as_bad (_("%s for instruction '%s'"), errmsg, opname);
      else
	as_bad (_("inappropriate arguments for opcode '%s'"), opname);
      return;
    }

  autodetect_attributes (opcode, tok, ntok);
  assemble_insn (opcode, tok, ntok, pflags, nflgs, &insn);
  emit_insn (&insn);
}

/* The public interface to the instruction assembler.  */

void
md_assemble (char *str)
{
  char *opname;
  expressionS tok[MAX_INSN_ARGS];
  int ntok, nflg;
  size_t opnamelen;
  struct arc_flags flags[MAX_INSN_FLGS];

  opnamelen = strspn (str, "abcdefghijklmnopqrstuvwxyz_0123456789");
  opname = xmemdup0 (str, opnamelen);

  assembling_insn = true;

  nflg = tokenize_flags (str + opnamelen, flags, MAX_INSN_FLGS);
  if (nflg == -1)
    {
      as_bad (_("syntax error"));
      assembling_insn = false;
      return;
    }

  str += opnamelen;
  while (!is_end_of_stmt (*str) && !is_whitespace (*str))
    str++;

  ntok = tokenize_arguments (str, tok, MAX_INSN_ARGS);
  if (ntok < 0)
    {
      as_bad (_("syntax error"));
      assembling_insn = false;
      return;
    }

  assemble_tokens (opname, tok, ntok, flags, nflg);
  assembling_insn = false;
}

/* Callback to insert a register into the hash table.  */

static void
declare_register (const char *name, int number)
{
  if (name == NULL)
    return;

  symbolS *regS = symbol_create (name, reg_section,
                                 &zero_address_frag, number);
  
  if (regS == NULL)
    {
      as_fatal (_("failed to create symbol for register %s"), name);
      return;
    }

  const char *symbol_name = S_GET_NAME (regS);
  if (symbol_name == NULL)
    {
      as_fatal (_("invalid symbol name for register %s"), name);
      return;
    }

  if (str_hash_insert (arc_reg_hash, symbol_name, regS, 0) != NULL)
    as_fatal (_("duplicate %s"), name);
}

/* Construct symbols for each of the general registers.  */

static void declare_register_set(void)
{
    for (int i = 0; i < 64; ++i)
    {
        char name[32];
        int result = snprintf(name, sizeof(name), "r%d", i);
        if (result > 0 && result < sizeof(name))
        {
            declare_register(name, i);
        }
        
        if ((i & 0x01) == 0)
        {
            result = snprintf(name, sizeof(name), "r%dr%d", i, i + 1);
            if (result > 0 && result < sizeof(name))
            {
                declare_register(name, i);
            }
        }
    }
}

/* Construct a symbol for an address type.  */

static void
declare_addrtype (const char *name, int number)
{
  if (name == NULL)
    {
      as_fatal (_("null address type name"));
      return;
    }

  symbolS *addrtypeS = symbol_create (name, undefined_section,
                                      &zero_address_frag, number);
  
  if (addrtypeS == NULL)
    {
      as_fatal (_("failed to create symbol for %s"), name);
      return;
    }

  const char *symbol_name = S_GET_NAME (addrtypeS);
  if (symbol_name == NULL)
    {
      as_fatal (_("failed to get symbol name for %s"), name);
      return;
    }

  if (str_hash_insert (arc_addrtype_hash, symbol_name, addrtypeS, 0))
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

  target_big_endian = byte_order == BIG_ENDIAN;

  if (!bfd_set_arch_mach (stdoutput, bfd_arch_arc, selected_cpu.mach))
    as_warn (_("could not set architecture and machine"));

  bfd_set_private_flags (stdoutput, selected_cpu.eflags);

  arc_opcode_hash = htab_create_alloc (16, hash_string_tuple, eq_string_tuple,
				       arc_opcode_free, xcalloc, free);

  while (opcode && opcode->name)
    {
      const char *name = opcode->name;
      arc_insert_opcode (opcode);
      opcode++;
      while (opcode && opcode->name && 
             (opcode->name == name || strcmp (opcode->name, name) == 0))
        opcode++;
    }

  arc_reg_hash = str_htab_create ();

  declare_register_set ();
  declare_register ("gp", 26);
  declare_register ("fp", 27);
  declare_register ("sp", 28);
  declare_register ("ilink", 29);
  declare_register ("ilink1", 29);
  declare_register ("ilink2", 30);
  declare_register ("blink", 31);

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

  memset (&arc_last_insns[0], 0, sizeof (arc_last_insns));

  arc_aux_hash = str_htab_create ();

  const struct arc_aux_reg *auxr = &arc_aux_regs[0];
  unsigned int i;
  for (i = 0; i < arc_num_aux_regs; i++, auxr++)
    {
      if ((auxr->cpu & selected_cpu.flags) == 0)
	continue;

      if (auxr->subclass != NONE && !check_cpu_feature (auxr->subclass))
	continue;

      if (str_hash_insert (arc_aux_hash, auxr->name, auxr, 0) != 0)
	as_fatal (_("duplicate %s"), auxr->name);
    }

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

void arc_md_end(void)
{
    if (arc_opcode_hash != NULL) {
        htab_delete(arc_opcode_hash);
        arc_opcode_hash = NULL;
    }
    
    if (arc_reg_hash != NULL) {
        htab_delete(arc_reg_hash);
        arc_reg_hash = NULL;
    }
    
    if (arc_aux_hash != NULL) {
        htab_delete(arc_aux_hash);
        arc_aux_hash = NULL;
    }
    
    if (arc_addrtype_hash != NULL) {
        htab_delete(arc_addrtype_hash);
        arc_addrtype_hash = NULL;
    }
}

/* Write a value out to the object file, using the appropriate
   endianness.  */

void md_number_to_chars(char *buf, valueT val, int n)
{
    if (buf == NULL || n <= 0) {
        return;
    }
    
    if (target_big_endian) {
        number_to_chars_bigendian(buf, val, n);
    } else {
        number_to_chars_littleendian(buf, val, n);
    }
}

/* Round up a section size to the appropriate boundary.  */

valueT
md_section_align (segT segment, valueT size)
{
  int align = bfd_section_alignment (segment);
  valueT alignment = (valueT)1 << align;
  valueT mask = alignment - 1;
  
  return (size + mask) & ~mask;
}

/* The location from which a PC relative jump should be calculated,
   given a PC relative reloc.  */

long
md_pcrel_from_section (fixS *fixP,
		       segT sec)
{
  offsetT base;
  
  if (fixP == NULL || fixP->fx_frag == NULL)
    return 0;
    
  base = fixP->fx_where + fixP->fx_frag->fr_address;

  pr_debug ("pcrel_from_section, fx_offset = %d\n", (int) fixP->fx_offset);

  if (fixP->fx_addsy != NULL
      && (!S_IS_DEFINED (fixP->fx_addsy)
	  || S_GET_SEGMENT (fixP->fx_addsy) != sec))
    {
      pr_debug ("Unknown pcrel symbol: %s\n", S_GET_NAME (fixP->fx_addsy));
      return 0;
    }

  if ((int) fixP->fx_r_type < 0)
    {
      base &= ~3;
    }
  else
    {
      switch (fixP->fx_r_type)
	{
	case BFD_RELOC_ARC_PC32:
	  base -= 4;
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
	  as_bad_where (fixP->fx_file, fixP->fx_line,
			_("unhandled reloc %s in md_pcrel_from_section"),
		  bfd_get_reloc_code_name (fixP->fx_r_type));
	  break;
	}
    }

  pr_debug ("pcrel from %" PRIx64 " + %lx = %" PRIx64 ", "
	    "symbol: %s (%" PRIx64 ")\n",
	    (uint64_t) fixP->fx_frag->fr_address, fixP->fx_where, (uint64_t) base,
	    fixP->fx_addsy ? S_GET_NAME (fixP->fx_addsy) : "(null)",
	    fixP->fx_addsy ? (uint64_t) S_GET_VALUE (fixP->fx_addsy) : (uint64_t) 0);

  return base;
}

/* Given a BFD relocation find the corresponding operand.  */

static const struct arc_operand *
find_operand_for_reloc (extended_bfd_reloc_code_real_type reloc)
{
  for (unsigned i = 0; i < arc_num_operands; i++)
    {
      if (arc_operands[i].default_reloc == reloc)
        return &arc_operands[i];
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
  if (operand == NULL || file == NULL)
    return insn;

  if (operand->bits != 32 && 
      !(operand->flags & (ARC_OPERAND_NCHK | ARC_OPERAND_FAKE)))
    {
      offsetT min = 0;
      offsetT max = 0;
      
      if (operand->flags & ARC_OPERAND_SIGNED)
	{
	  max = (1LL << (operand->bits - 1)) - 1;
	  min = -(1LL << (operand->bits - 1));
	}
      else
	{
	  max = (1LL << operand->bits) - 1;
	  min = 0;
	}

      if (val < min || val > max)
	as_bad_value_out_of_range (_("operand"),
				   val, min, max, file, line);
      
      pr_debug ("insert field: %ld <= %lld <= %ld in 0x%08llx\n",
	        min, val, max, insn);
    }
  else
    {
      pr_debug ("insert field: %lld in 0x%08llx\n", val, insn);
    }

  if ((operand->flags & ARC_OPERAND_ALIGNED32) && (val & 0x03))
    as_bad_where (file, line,
		  _("Unaligned operand. Needs to be 32bit aligned"));

  if ((operand->flags & ARC_OPERAND_ALIGNED16) && (val & 0x01))
    as_bad_where (file, line,
		  _("Unaligned operand. Needs to be 16bit aligned"));

  if (operand->insert)
    {
      const char *errmsg = NULL;
      insn = (*operand->insert) (insn, val, &errmsg);
      if (errmsg)
	as_warn_where (file, line, "%s", errmsg);
    }
  else
    {
      long long adjusted_val = val;
      
      if (operand->flags & ARC_OPERAND_TRUNCATE)
	{
	  if (operand->flags & ARC_OPERAND_ALIGNED32)
	    adjusted_val >>= 2;
	  if (operand->flags & ARC_OPERAND_ALIGNED16)
	    adjusted_val >>= 1;
	}
      
      unsigned long long mask = (1ULL << operand->bits) - 1;
      insn |= ((adjusted_val & mask) << operand->shift);
    }
  
  return insn;
}

/* Apply a fixup to the object code.  At this point all symbol values
   should be fully resolved, and we attempt to completely resolve the
   reloc.  If we can not do that, we determine the correct reloc code
   and put it back in the fixup.  To indicate that a fixup has been
   eliminated, set fixP->fx_done.  */

void
md_apply_fix (fixS *fixP,
	      valueT *valP,
	      segT seg)
{
  char * const fixpos = fixP->fx_frag->fr_literal + fixP->fx_where;
  valueT value = *valP;
  unsigned insn = 0;
  symbolS *fx_addsy, *fx_subsy;
  offsetT fx_offset;
  segT add_symbol_segment = absolute_section;
  segT sub_symbol_segment = absolute_section;
  const struct arc_operand *operand = NULL;
  extended_bfd_reloc_code_real_type reloc;

  pr_debug ("%s:%u: apply_fix: r_type=%d (%s) value=0x%lX offset=0x%lX\n",
	    fixP->fx_file, fixP->fx_line, fixP->fx_r_type,
	    ((int) fixP->fx_r_type < 0) ? "Internal":
	    bfd_get_reloc_code_name (fixP->fx_r_type), value,
	    fixP->fx_offset);

  fx_addsy = fixP->fx_addsy;
  fx_subsy = fixP->fx_subsy;
  fx_offset = 0;

  if (fx_addsy)
    {
      add_symbol_segment = S_GET_SEGMENT (fx_addsy);
    }

  if (fx_subsy
      && fixP->fx_r_type != BFD_RELOC_ARC_TLS_DTPOFF
      && fixP->fx_r_type != BFD_RELOC_ARC_TLS_DTPOFF_S9
      && fixP->fx_r_type != BFD_RELOC_ARC_TLS_GD_LD)
    {
      resolve_symbol_value (fx_subsy);
      sub_symbol_segment = S_GET_SEGMENT (fx_subsy);

      if (sub_symbol_segment == absolute_section)
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

  if (!fx_addsy)
    fixP->fx_done = true;

  if (fixP->fx_pcrel)
    {
      if (fx_addsy
	  && ((S_IS_DEFINED (fx_addsy)
	       && S_GET_SEGMENT (fx_addsy) != seg)
	      || S_IS_WEAK (fx_addsy)))
	value += md_pcrel_from_section (fixP, seg);

      switch (fixP->fx_r_type)
	{
	case BFD_RELOC_ARC_32_ME:
	  fixP->fx_offset += fixP->fx_frag->fr_address;
	  fixP->fx_r_type = BFD_RELOC_ARC_PC32;
	  break;
	case BFD_RELOC_32:
	  fixP->fx_r_type = BFD_RELOC_ARC_PC32;
	  break;
	case BFD_RELOC_ARC_PC32:
	  break;
	default:
	  if ((int) fixP->fx_r_type < 0)
	    as_bad_where (fixP->fx_file, fixP->fx_line,
			  _("PC relative relocation not allowed for (internal)"
			    " type %d"),
			  fixP->fx_r_type);
	  break;
	}
    }

  pr_debug ("%s:%u: apply_fix: r_type=%d (%s) value=0x%lX offset=0x%lX\n",
	    fixP->fx_file, fixP->fx_line, fixP->fx_r_type,
	    ((int) fixP->fx_r_type < 0) ? "Internal":
	    bfd_get_reloc_code_name (fixP->fx_r_type), value,
	    fixP->fx_offset);

  reloc = fixP->fx_r_type;
  switch (reloc)
    {
    case BFD_RELOC_ARC_TLS_DTPOFF:
    case BFD_RELOC_ARC_TLS_LE_32:
      if (!fixP->fx_done)
	{
	  S_SET_THREAD_LOCAL (fixP->fx_addsy);
	}
      break;
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
      S_SET_THREAD_LOCAL (fixP->fx_addsy);
      break;
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

  if (!fixP->fx_done)
    {
      return;
    }

  value += fx_offset;

  if (value & 0x80000000)
    value |= (-1UL << 31);

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
      md_number_to_chars_midend (fixpos, value, fixP->fx_size);
      return;
    case BFD_RELOC_ARC_GOTOFF:
    case BFD_RELOC_ARC_32_ME:
    case BFD_RELOC_ARC_PC32:
    case BFD_RELOC_ARC_PLT32:
      md_number_to_chars_midend (fixpos, value, fixP->fx_size);
      return;
    case BFD_RELOC_ARC_S25H_PCREL_PLT:
      reloc = BFD_RELOC_ARC_S25W_PCREL;
      break;
    case BFD_RELOC_ARC_S21H_PCREL_PLT:
      reloc = BFD_RELOC_ARC_S21H_PCREL;
      break;
    case BFD_RELOC_ARC_S25W_PCREL_PLT:
      reloc = BFD_RELOC_ARC_S25W_PCREL;
      break;
    case BFD_RELOC_ARC_S21W_PCREL_PLT:
      reloc = BFD_RELOC_ARC_S21W_PCREL;
      break;
    case BFD_RELOC_ARC_S25W_PCREL:
    case BFD_RELOC_ARC_S21W_PCREL:
    case BFD_RELOC_ARC_S21H_PCREL:
    case BFD_RELOC_ARC_S25H_PCREL:
    case BFD_RELOC_ARC_S13_PCREL:
      break;
    default:
      if ((int) fixP->fx_r_type >= 0)
	{
	  as_fatal (_("unhandled relocation type %s"),
		    bfd_get_reloc_code_name (fixP->fx_r_type));
	}
      if (fixP->fx_addsy != 0
	  && S_GET_SEGMENT (fixP->fx_addsy) != absolute_section)
	{
	  as_bad_where (fixP->fx_file, fixP->fx_line,
			_("non-absolute expression in constant field"));
	}
      gas_assert (-(int) fixP->fx_r_type < (int) arc_num_operands);
      operand = &arc_operands[-(int) fixP->fx_r_type];
      break;
    }

  if (operand == NULL)
    {
      operand = find_operand_for_reloc (reloc);
      gas_assert (operand);
    }

  if (target_big_endian)
    {
      switch (fixP->fx_size)
	{
	case 4:
	  insn = bfd_getb32 (fixpos);
	  break;
	case 2:
	  insn = bfd_getb16 (fixpos);
	  break;
	default:
	  as_bad_where (fixP->fx_file, fixP->fx_line,
			_("unknown fixup size"));
	  return;
	}
    }
  else
    {
      switch (fixP->fx_size)
	{
	case 4:
	  insn = bfd_getl16 (fixpos) << 16 | bfd_getl16 (fixpos + 2);
	  break;
	case 2:
	  insn = bfd_getl16 (fixpos);
	  break;
	default:
	  as_bad_where (fixP->fx_file, fixP->fx_line,
			_("unknown fixup size"));
	  return;
	}
    }

  insn = insert_operand (insn, operand, (offsetT) value,
			 fixP->fx_file, fixP->fx_line);

  md_number_to_chars_midend (fixpos, insn, fixP->fx_size);
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

int
md_estimate_size_before_relax (fragS *fragP,
			       segT segment)
{
  if (fragP == NULL) {
    return 0;
  }

  if (fragP->fr_symbol == NULL) {
    return 0;
  }

  if (should_use_maximum_size(fragP, segment)) {
    advance_to_maximum_subtype(fragP);
  }

  int growth = md_relax_table[fragP->fr_subtype].rlx_length;
  fragP->fr_var = growth;

  pr_debug ("%s:%d: md_estimate_size_before_relax: %d\n",
	   fragP->fr_file, fragP->fr_line, growth);

  return growth;
}

static int
should_use_maximum_size(fragS *fragP, segT segment)
{
  segT symbol_segment = S_GET_SEGMENT(fragP->fr_symbol);
  
  if (symbol_segment != segment && symbol_segment != absolute_section) {
    return 1;
  }
  
  if (symbol_constant_p(fragP->fr_symbol) && !fragP->tc_frag_data.pcrel) {
    return 1;
  }
  
  if (symbol_equated_p(fragP->fr_symbol)) {
    return 1;
  }
  
  if (S_IS_WEAK(fragP->fr_symbol)) {
    return 1;
  }
  
  return 0;
}

static void
advance_to_maximum_subtype(fragS *fragP)
{
  while (md_relax_table[fragP->fr_subtype].rlx_more != ARC_RLX_NONE) {
    fragP->fr_subtype++;
  }
}

/* Translate internal representation of relocation info to BFD target
   format.  */

arelent *
tc_gen_reloc (asection *section ATTRIBUTE_UNUSED,
	      fixS *fixP)
{
  arelent *reloc;
  bfd_reloc_code_real_type code;

  if (!fixP)
    return NULL;

  reloc = notes_alloc (sizeof (arelent));
  if (!reloc)
    return NULL;

  reloc->sym_ptr_ptr = notes_alloc (sizeof (asymbol *));
  if (!reloc->sym_ptr_ptr)
    return NULL;

  *reloc->sym_ptr_ptr = symbol_get_bfdsym (fixP->fx_addsy);
  reloc->address = fixP->fx_frag->fr_address + fixP->fx_where;

  gas_assert ((int) fixP->fx_r_type > 0);

  code = fixP->fx_r_type;

  if (code == BFD_RELOC_ARC_GOTPC32
      && GOT_symbol
      && fixP->fx_addsy == GOT_symbol)
    code = BFD_RELOC_ARC_GOTPC;

  reloc->howto = bfd_reloc_type_lookup (stdoutput, code);
  if (!reloc->howto)
    {
      as_bad_where (fixP->fx_file, fixP->fx_line,
		    _("cannot represent `%s' relocation in object file"),
		    bfd_get_reloc_code_name (code));
      return NULL;
    }

  bool pc_relative_mismatch = (fixP->fx_pcrel != 0) != (reloc->howto->pc_relative != 0);
  if (pc_relative_mismatch)
    as_fatal (_("internal error? cannot generate `%s' relocation"),
	      bfd_get_reloc_code_name (code));

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
  const relax_typeS *table_entry;
  char *dest;
  const struct arc_opcode *opcode;
  struct arc_insn insn;
  int size, fix;
  struct arc_relax_type *relax_arg = &fragP->tc_frag_data;

  fix = fragP->fr_fix;
  dest = fragP->fr_literal + fix;
  table_entry = TC_GENERIC_RELAX_TABLE + fragP->fr_subtype;

  pr_debug ("%s:%d: md_convert_frag, subtype: %d, fix: %d, "
	    "var: %" PRId64 "\n",
	    fragP->fr_file, fragP->fr_line,
	    fragP->fr_subtype, fix, (int64_t) fragP->fr_var);

  if (fragP->fr_subtype < 0
      || fragP->fr_subtype >= arc_num_relax_opcodes)
    as_fatal (_("no relaxation found for this instruction."));

  opcode = &arc_relax_opcodes[fragP->fr_subtype];

  assemble_insn (opcode, relax_arg->tok, relax_arg->ntok, relax_arg->pflags,
	relax_arg->nflg, &insn);

  apply_fixups (&insn, fragP, fix);

  size = insn.len + (insn.has_limm ? 4 : 0);
  gas_assert (table_entry->rlx_length == size);
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
  if (name == NULL) {
    return NULL;
  }

  if (strcmp(name, GLOBAL_OFFSET_TABLE_NAME) != 0) {
    return NULL;
  }

  if (GOT_symbol != NULL) {
    return GOT_symbol;
  }

  if (symbol_find(name) != NULL) {
    as_bad("GOT already in symbol table");
    return NULL;
  }

  GOT_symbol = symbol_new(GLOBAL_OFFSET_TABLE_NAME, undefined_section,
                         &zero_address_frag, 0);
  
  return GOT_symbol;
}

/* Turn a string in input_line_pointer into a floating point constant
   of type type, and store the appropriate bytes in *litP.  The number
   of LITTLENUMS emitted is stored in *sizeP.  An error message is
   returned, or NULL on OK.  */

const char *md_atof(int type, char *litP, int *sizeP)
{
    if (litP == NULL || sizeP == NULL) {
        return "Invalid parameters";
    }
    
    return ieee_md_atof(type, litP, sizeP, target_big_endian);
}

/* Called for any expression that can not be recognized.  When the
   function is called, `input_line_pointer' will point to the start of
   the expression.  We use it when we have complex operations like
   @label1 - @label2.  */

void
md_operand (expressionS *expressionP)
{
  if (input_line_pointer == NULL || expressionP == NULL)
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
  struct symbol *sym;

  if (!assembling_insn)
    return false;

  if (e->X_op == O_symbol && e->X_md == O_absent)
    return false;

  if (name == NULL)
    return false;

  sym = str_hash_find (arc_reg_hash, name);
  if (sym != NULL)
    {
      e->X_op = O_register;
      e->X_add_number = S_GET_VALUE (sym);
      return true;
    }

  sym = str_hash_find (arc_addrtype_hash, name);
  if (sym != NULL)
    {
      e->X_op = O_addrtype;
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

int
md_parse_option (int c, const char *arg ATTRIBUTE_UNUSED)
{
  switch (c)
    {
    case OPTION_ARC600:
    case OPTION_ARC601:
      return md_parse_option (OPTION_MCPU, "arc600");

    case OPTION_ARC700:
      return md_parse_option (OPTION_MCPU, "arc700");

    case OPTION_ARCEM:
      return md_parse_option (OPTION_MCPU, "arcem");

    case OPTION_ARCHS:
      return md_parse_option (OPTION_MCPU, "archs");

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
      selected_cpu.features |= CD;
      cl_features |= CD;
      arc_check_feature ();
      break;

    case OPTION_RELAX:
      relaxation_state = 1;
      break;

    case OPTION_NPS400:
      selected_cpu.features |= NPS400;
      cl_features |= NPS400;
      arc_check_feature ();
      break;

    case OPTION_SPFP:
      selected_cpu.features |= SPX;
      cl_features |= SPX;
      arc_check_feature ();
      break;

    case OPTION_DPFP:
      selected_cpu.features |= DPX;
      cl_features |= DPX;
      arc_check_feature ();
      break;

    case OPTION_FPUDA:
      selected_cpu.features |= DPA;
      cl_features |= DPA;
      arc_check_feature ();
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
  const char *space_buf = "                          ";
  const int space_len = 26;
  const int max_width = 80;
  int offset = space_len;
  
  if (!stream)
    return;
  
  if (fprintf(stream, "%s", space_buf) < 0)
    return;
  
  for (int i = 0; cpu_types[i].name != NULL; ++i)
    {
      const char *name = cpu_types[i].name;
      int name_len = strlen(name);
      bool last = (cpu_types[i + 1].name == NULL);
      int extra_len = last ? 0 : 2;
      
      if (offset + name_len + extra_len > max_width)
        {
          if (fprintf(stream, "\n%s", space_buf) < 0)
            return;
          offset = space_len;
        }
      
      if (fprintf(stream, "%s%s", name, last ? "\n" : ", ") < 0)
        return;
      
      offset += name_len + extra_len;
    }
}

void
md_show_usage (FILE *stream)
{
  if (stream == NULL)
    return;

  fprintf (stream, _("ARC-specific assembler options:\n"));

  fprintf (stream, "  -mcpu=<cpu name>\t  (default: %s), assemble for"
           " CPU <cpu name>, one of:\n", TARGET_WITH_CPU);
  arc_show_cpu_list (stream);
  fprintf (stream, "\n");
  fprintf (stream, "  -mA6/-mARC600/-mARC601  same as -mcpu=arc600\n");
  fprintf (stream, "  -mA7/-mARC700\t\t  same as -mcpu=arc700\n");
  fprintf (stream, "  -mEM\t\t\t  same as -mcpu=arcem\n");
  fprintf (stream, "  -mHS\t\t\t  same as -mcpu=archs\n");

  fprintf (stream, "  -mnps400\t\t  enable NPS-400 extended instructions\n");
  fprintf (stream, "  -mspfp\t\t  enable single-precision floating point"
	   " instructions\n");
  fprintf (stream, "  -mdpfp\t\t  enable double-precision floating point"
	   " instructions\n");
  fprintf (stream, "  -mfpuda\t\t  enable double-precision assist floating "
                   "point\n\t\t\t  instructions for ARC EM\n");

  fprintf (stream,
	   "  -mcode-density\t  enable code density option for ARC EM\n");

  fprintf (stream, _("\
  -EB                     assemble code for a big-endian cpu\n"));
  fprintf (stream, _("\
  -EL                     assemble code for a little-endian cpu\n"));
  fprintf (stream, _("\
  -mrelax                 enable relaxation\n"));

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

static extended_bfd_reloc_code_real_type
find_reloc (const char *name,
	    const char *opcodename,
	    const struct arc_flags *pflags,
	    int nflg,
	    extended_bfd_reloc_code_real_type reloc)
{
  if (!name || !opcodename) {
    return BFD_RELOC_UNUSED;
  }

  for (unsigned int i = 0; i < arc_num_equiv_tab; i++) {
    const struct arc_reloc_equiv_tab *r = &arc_reloc_equiv[i];

    if (strcmp(name, r->name) != 0) {
      continue;
    }

    if (r->mnemonic && strcmp(r->mnemonic, opcodename) != 0) {
      continue;
    }

    if (r->flags[0] && !match_flags(r->flags, pflags, nflg)) {
      continue;
    }

    if (reloc != r->oldreloc) {
      continue;
    }

    return r->newreloc;
  }

  as_bad(_("Unable to find %s relocation for instruction %s"),
         name, opcodename);
  return BFD_RELOC_UNUSED;
}

static bool
match_flags(const unsigned *required_flags,
            const struct arc_flags *provided_flags,
            int nflg)
{
  if (!required_flags || !provided_flags || nflg <= 0) {
    return false;
  }

  for (const unsigned *flag = required_flags; *flag; flag++) {
    if (!has_flag(provided_flags, nflg, *flag)) {
      return false;
    }
  }

  return true;
}

static bool
has_flag(const struct arc_flags *flags, int nflg, unsigned flag_index)
{
  const char *flag_name = arc_flag_operands[flag_index].name;
  
  for (int i = 0; i < nflg; i++) {
    if (strcmp(flags[i].name, flag_name) == 0) {
      return true;
    }
  }
  
  return false;
}

/* All the symbol types that are allowed to be used for
   relaxation.  */

static bool
may_relax_expr (expressionS tok)
{
  if (tok.X_md == O_plt)
    return false;

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
  if (!ins || !pflags || nflgs <= 0)
    return false;

  int counttrue = 0;

  for (unsigned flag_class_idx = 0; ins->flag_classes[flag_class_idx] != 0; flag_class_idx++)
    {
      unsigned flag_class = ins->flag_classes[flag_class_idx];
      
      for (unsigned flag_idx = 0; arc_flag_classes[flag_class].flags[flag_idx] != 0; flag_idx++)
        {
          unsigned flag = arc_flag_classes[flag_class].flags[flag_idx];
          const struct arc_flag_operand *flag_opand = &arc_flag_operands[flag];
          
          for (int i = 0; i < nflgs; i++)
            {
              if (strcmp (flag_opand->name, pflags[i].name) == 0)
                {
                  counttrue++;
                  if (counttrue == nflgs)
                    return true;
                }
            }
        }
    }

  return counttrue == nflgs;
}

/* Checks if operands are in line with relaxable insn.  */

static bool
relaxable_operand (const struct arc_relaxable_ins *ins,
		   const expressionS *tok,
		   int ntok)
{
  const enum rlx_operand_type *operand = &ins->operands[0];
  int i = 0;

  while (*operand != EMPTY)
    {
      if (i >= ntok)
	return false;

      const expressionS *epr = &tok[i];

      switch (*operand)
	{
	case IMMEDIATE:
	  if (epr->X_op != O_multiply
		&& epr->X_op != O_divide
		&& epr->X_op != O_modulus
		&& epr->X_op != O_add
		&& epr->X_op != O_subtract
		&& epr->X_op != O_symbol)
	    return false;
	  break;

	case REGISTER_DUP:
	  if (i == 0
	      || epr->X_add_number != tok[i - 1].X_add_number)
	    return false;
	case REGISTER:
	  if (epr->X_op != O_register)
	    return false;
	  break;

	case REGISTER_S:
	  if (epr->X_op != O_register)
	    return false;

	  switch (epr->X_add_number)
	    {
	    case 0: case 1: case 2: case 3:
	    case 12: case 13: case 14: case 15:
	      break;
	    default:
	      return false;
	    }
	  break;

	case REGISTER_NO_GP:
	  if (epr->X_op != O_register
	      || epr->X_add_number == 26)
	    return false;
	  break;

	case BRACKET:
	  if (epr->X_op != O_bracket)
	    return false;
	  break;

	default:
	  return false;
	}

      ++i;
      operand = &ins->operands[i];
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
  if (!relaxation_state || !opcode || !tok || ntok <= 0)
    return false;

  for (unsigned i = 0; i < arc_num_relaxable_ins; ++i)
    {
      const struct arc_relaxable_ins *arc_rlx_ins = &arc_relaxable_insns[i];

      if (!arc_rlx_ins || !arc_rlx_ins->mnemonic_r)
        continue;

      if (strcmp(opcode->name, arc_rlx_ins->mnemonic_r) != 0)
        continue;

      if (arc_rlx_ins->opcheckidx >= ntok)
        continue;

      if (!may_relax_expr(tok[arc_rlx_ins->opcheckidx]))
        continue;

      if (!relaxable_operand(arc_rlx_ins, tok, ntok))
        continue;

      if (!relaxable_flag(arc_rlx_ins, pflags, nflg))
        continue;

      if (!frag_now)
        return false;

      frag_now->fr_subtype = arc_rlx_ins->subtype;
      
      if (ntok > 0 && ntok <= MAX_INSN_ARGS)
        memcpy(&frag_now->tc_frag_data.tok, tok, sizeof(expressionS) * ntok);
      
      if (nflg > 0 && nflg <= MAX_INSN_FLGS && pflags)
        memcpy(&frag_now->tc_frag_data.pflags, pflags, sizeof(struct arc_flags) * nflg);
      
      frag_now->tc_frag_data.nflg = nflg;
      frag_now->tc_frag_data.ntok = ntok;
      
      return true;
    }

  return false;
}

/* Turn an opcode description and a set of arguments into
   an instruction and a fixup.  */

static void
assemble_insn (const struct arc_opcode *opcode,
	       const expressionS *tok,
	       int ntok,
	       const struct arc_flags *pflags,
	       int nflg,
	       struct arc_insn *insn)
{
  const expressionS *reloc_exp = NULL;
  unsigned long long image;
  const unsigned char *argidx;
  int i;
  int tokidx = 0;
  unsigned char pcrel = 0;
  bool needGOTSymbol;
  bool has_delay_slot = false;
  extended_bfd_reloc_code_real_type reloc = BFD_RELOC_UNUSED;

  memset (insn, 0, sizeof (*insn));
  image = opcode->opcode;

  pr_debug ("%s:%d: assemble_insn: %s using opcode %llx\n",
	    frag_now->fr_file, frag_now->fr_line, opcode->name,
	    opcode->opcode);

  for (argidx = opcode->operands; *argidx; ++argidx)
    {
      const struct arc_operand *operand = &arc_operands[*argidx];
      const expressionS *t = NULL;

      if (ARC_OPERAND_IS_FAKE (operand))
	continue;

      if (operand->flags & ARC_OPERAND_DUPLICATE)
	{
	  tokidx++;
	  continue;
	}

      if (tokidx >= ntok)
	abort ();
      
      t = &tok[tokidx++];

      if (operand->flags & ARC_OPERAND_LIMM)
	insn->has_limm = true;

      if (t->X_op == O_register)
	{
	  image = insert_operand (image, operand, regno (t->X_add_number),
				  NULL, 0);
	}
      else if (t->X_op == O_constant)
	{
	  image = insert_operand (image, operand, t->X_add_number, NULL, 0);
	  reloc_exp = t;
	  if (operand->flags & ARC_OPERAND_LIMM)
	    insn->limm = t->X_add_number;
	}
      else if (t->X_op == O_bracket || t->X_op == O_colon || t->X_op == O_addrtype)
	{
	  continue;
	}
      else if (t->X_op == O_absent)
	{
	  gas_assert (operand->flags & ARC_OPERAND_IGNORE);
	}
      else if (t->X_op == O_subtract)
	{
	  if ((t->X_add_number == 0)
	      && contains_register (t->X_add_symbol)
	      && contains_register (t->X_op_symbol))
	    {
	      int regs;
	      regs = get_register (t->X_add_symbol);
	      regs <<= 16;
	      regs |= get_register (t->X_op_symbol);
	      image = insert_operand (image, operand, regs, NULL, 0);
	      continue;
	    }
	  needGOTSymbol = false;
	  reloc = process_relocation (t, opcode, operand, pflags, nflg, &needGOTSymbol);
	  if (needGOTSymbol && (GOT_symbol == NULL))
	    GOT_symbol = symbol_find_or_make (GLOBAL_OFFSET_TABLE_NAME);
	  reloc_exp = t;
	  add_fixup (insn, t, reloc, operand, &pcrel);
	}
      else
	{
	  needGOTSymbol = false;
	  reloc = process_relocation (t, opcode, operand, pflags, nflg, &needGOTSymbol);
	  if (needGOTSymbol && (GOT_symbol == NULL))
	    GOT_symbol = symbol_find_or_make (GLOBAL_OFFSET_TABLE_NAME);
	  reloc_exp = t;
	  add_fixup (insn, t, reloc, operand, &pcrel);
	}
    }

  for (i = 0; i < nflg; i++)
    {
      const struct arc_flag_operand *flg_operand = pflags[i].flgp;

      if (!strcmp (flg_operand->name, "d"))
	has_delay_slot = true;

      if ((selected_cpu.flags & ARC_OPCODE_ARCV2)
	  && (!strcmp (flg_operand->name, "t")
	      || !strcmp (flg_operand->name, "nt")))
	{
	  image = process_conditional_flag (opcode, flg_operand, reloc_exp, 
					     insn, image, pcrel);
	}
      else
	{
	  image |= (flg_operand->code & ((1 << flg_operand->bits) - 1))
	    << flg_operand->shift;
	}
    }

  insn->relax = relax_insn_p (opcode, tok, ntok, pflags, nflg);
  insn->len = arc_opcode_len (opcode);
  insn->insn = image;

  arc_last_insns[1] = arc_last_insns[0];
  arc_last_insns[0].opcode = opcode;
  arc_last_insns[0].has_limm = insn->has_limm;
  arc_last_insns[0].has_delay_slot = has_delay_slot;

  validate_instruction_sequence ();
}

static extended_bfd_reloc_code_real_type
process_relocation (const expressionS *t, const struct arc_opcode *opcode,
		    const struct arc_operand *operand,
		    const struct arc_flags *pflags, int nflg,
		    bool *needGOTSymbol)
{
  extended_bfd_reloc_code_real_type reloc = BFD_RELOC_UNUSED;

  switch (t->X_md)
    {
    case O_plt:
      if (opcode->insn_class == JUMP)
	as_bad (_("Unable to use @plt relocation for insn %s"),
		opcode->name);
      *needGOTSymbol = true;
      reloc = find_reloc ("plt", opcode->name, pflags, nflg,
			  operand->default_reloc);
      break;

    case O_gotoff:
    case O_gotpc:
      *needGOTSymbol = true;
      reloc = ARC_RELOC_TABLE (t->X_md)->reloc;
      break;

    case O_pcl:
      if (operand->flags & ARC_OPERAND_LIMM)
	{
	  reloc = ARC_RELOC_TABLE (t->X_md)->reloc;
	  if (arc_opcode_len (opcode) == 2 || opcode->insn_class == JUMP)
	    as_bad (_("Unable to use @pcl relocation for insn %s"),
		    opcode->name);
	}
      else
	{
	  reloc = operand->default_reloc;
	}
      break;

    case O_sda:
      reloc = find_reloc ("sda", opcode->name, pflags, nflg,
			  operand->default_reloc);
      break;

    case O_tlsgd:
    case O_tlsie:
      *needGOTSymbol = true;
    case O_tpoff:
    case O_dtpoff:
      reloc = ARC_RELOC_TABLE (t->X_md)->reloc;
      break;

    case O_tpoff9:
    case O_dtpoff9:
      as_bad (_("TLS_*_S9 relocs are not supported yet"));
      break;

    default:
      reloc = operand->default_reloc;
      break;
    }

  return reloc;
}

static void
add_fixup (struct arc_insn *insn, const expressionS *t,
	   extended_bfd_reloc_code_real_type reloc,
	   const struct arc_operand *operand, unsigned char *pcrel)
{
  struct arc_fixup *fixup;

  if (insn->nfixups >= MAX_INSN_FIXUPS)
    as_fatal (_("too many fixups"));

  fixup = &insn->fixups[insn->nfixups++];
  fixup->exp = *t;
  fixup->reloc = reloc;

  if ((int) reloc < 0)
    {
      *pcrel = (operand->flags & ARC_OPERAND_PCREL) ? 1 : 0;
    }
  else
    {
      reloc_howto_type *reloc_howto = bfd_reloc_type_lookup (stdoutput, fixup->reloc);
      *pcrel = reloc_howto->pc_relative;
    }

  fixup->pcrel = *pcrel;
  fixup->islong = (operand->flags & ARC_OPERAND_LIMM) != 0;
}

static unsigned long long
process_conditional_flag (const struct arc_opcode *opcode,
			  const struct arc_flag_operand *flg_operand,
			  const expressionS *reloc_exp,
			  struct arc_insn *insn,
			  unsigned long long image,
			  unsigned char pcrel)
{
  unsigned bitYoperand = 0;
  bool is_bbit = (!strcmp (opcode->name, "bbit0") || !strcmp (opcode->name, "bbit1"));
  bool is_t_flag = !strcmp (flg_operand->name, "t");

  if (is_t_flag)
    bitYoperand = is_bbit ? arc_NToperand : arc_Toperand;
  else
    bitYoperand = is_bbit ? arc_Toperand : arc_NToperand;

  gas_assert (reloc_exp != NULL);

  if (reloc_exp->X_op == O_constant)
    {
      offsetT val = reloc_exp->X_add_number;
      image |= insert_operand (image, &arc_operands[bitYoperand], val, NULL, 0);
    }
  else
    {
      struct arc_fixup *fixup;

      if (insn->nfixups >= MAX_INSN_FIXUPS)
	as_fatal (_("too many fixups"));

      fixup = &insn->fixups[insn->nfixups++];
      fixup->exp = *reloc_exp;
      fixup->reloc = -bitYoperand;
      fixup->pcrel = pcrel;
      fixup->islong = false;
    }

  return image;
}

static void
validate_instruction_sequence (void)
{
  if (arc_last_insns[1].has_delay_slot && is_br_jmp_insn_p (arc_last_insns[0].opcode))
    {
      as_bad (_("Insn %s has a jump/branch instruction %s in its delay slot."),
	      arc_last_insns[1].opcode->name,
	      arc_last_insns[0].opcode->name);
    }

  if (arc_last_insns[1].has_delay_slot && arc_last_insns[0].has_limm)
    {
      as_bad (_("Insn %s has an instruction %s with limm in its delay slot."),
	      arc_last_insns[1].opcode->name,
	      arc_last_insns[0].opcode->name);
    }
}

void arc_handle_align(fragS *fragP)
{
    if (fragP == NULL || fragP->fr_type != rs_align_code) {
        return;
    }

    if (fragP->fr_next == NULL) {
        return;
    }

    char *dest = fragP->fr_literal + fragP->fr_fix;
    valueT count = fragP->fr_next->fr_address - fragP->fr_address - fragP->fr_fix;

    fragP->fr_var = 2;

    if (count & 1) {
        fragP->fr_fix++;
        *dest = 0;
        dest++;
    }

    md_number_to_chars(dest, NOP_OPCODE_S, 2);
}

/* Here we decide which fixups can be adjusted to make them relative
   to the beginning of the section instead of the symbol.  Basically
   we need to make sure that the dynamic relocations are done
   correctly, so in some cases we force the original symbol to be
   used.  */

int
tc_arc_fix_adjustable (fixS *fixP)
{
  if (S_IS_EXTERNAL (fixP->fx_addsy) || S_IS_WEAK (fixP->fx_addsy))
    return 0;

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
    return;

  if (*r_type_p != BFD_RELOC_32)
    return;

  if (exp->X_op != O_subtract)
    return;

  if (exp->X_op_symbol == NULL)
    return;

  if (S_GET_SEGMENT (exp->X_op_symbol) != now_seg)
    return;

  *r_type_p = BFD_RELOC_ARC_32_PCREL;
}


/* Add expression EXP of SIZE bytes to offset OFF of fragment FRAG.  */

void
arc_cons_fix_new (fragS *frag,
		  int off,
		  int size,
		  expressionS *exp,
		  bfd_reloc_code_real_type r_type)
{
  static const bfd_reloc_code_real_type size_to_reloc[] = {
    [1] = BFD_RELOC_8,
    [2] = BFD_RELOC_16,
    [3] = BFD_RELOC_24,
    [4] = BFD_RELOC_32,
    [8] = BFD_RELOC_64
  };

  if (size < 1 || size > 8 || (size > 4 && size != 8)) {
    as_bad (_("unsupported BFD relocation size %u"), size);
    r_type = BFD_RELOC_UNUSED;
  } else {
    r_type = size_to_reloc[size];
    if (size == 4) {
      arc_check_reloc (exp, &r_type);
    }
  }

  fix_new_exp (frag, off, size, exp, 0, r_type);
}

/* The actual routine that checks the ZOL conditions.  */

static void
check_zol (symbolS *s)
{
  const char *symbol_name = S_GET_NAME(s);
  
  if (selected_cpu.mach == bfd_mach_arc_arcv2)
    {
      if (selected_cpu.flags & ARC_OPCODE_ARCv2EM)
        return;
        
      if (is_br_jmp_insn_p(arc_last_insns[0].opcode) || 
          arc_last_insns[1].has_delay_slot)
        {
          as_bad(_("Jump/Branch instruction detected at the end of the ZOL label @%s"),
                 symbol_name);
        }
      return;
    }
  
  if (selected_cpu.mach == bfd_mach_arc_arc600)
    {
      if (is_kernel_insn_p(arc_last_insns[0].opcode))
        {
          as_bad(_("Kernel instruction detected at the end of the ZOL label @%s"),
                 symbol_name);
        }
        
      if (arc_last_insns[0].has_limm && 
          is_br_jmp_insn_p(arc_last_insns[0].opcode))
        {
          as_bad(_("A jump instruction with long immediate detected at the end of the ZOL label @%s"),
                 symbol_name);
        }
    }
  
  if (selected_cpu.mach == bfd_mach_arc_arc600 || 
      selected_cpu.mach == bfd_mach_arc_arc700)
    {
      if (arc_last_insns[0].has_delay_slot)
        {
          as_bad(_("An illegal use of delay slot detected at the end of the ZOL label @%s"),
                 symbol_name);
        }
    }
}

/* If ZOL end check the last two instruction for illegals.  */
void
arc_frob_label (symbolS * sym)
{
  if (sym == NULL)
    return;
    
  if (ARC_GET_FLAG (sym) & ARC_FLAG_ZOL)
    check_zol (sym);

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
  if (fragP == NULL)
    return 0;

  pr_debug ("arc_pcrel_adjust: address=%ld, fix=%ld, PCrel %s\n",
	    fragP->fr_address, fragP->fr_fix,
	    fragP->tc_frag_data.pcrel ? "Y" : "N");

  long result = fragP->fr_address + fragP->fr_fix;

  if (!fragP->tc_frag_data.pcrel)
    return result;

  return result & 0x03;
}

/* Initialize the DWARF-2 unwind information for this procedure.  */

void tc_arc_frame_initial_instructions(void)
{
    const int STACK_POINTER_REGISTER = 28;
    const int INITIAL_OFFSET = 0;
    
    cfi_add_CFA_def_cfa(STACK_POINTER_REGISTER, INITIAL_OFFSET);
}

int
tc_arc_regname_to_dw2regnum (char *regname)
{
  struct symbol *sym;

  if (regname == NULL || arc_reg_hash == NULL)
    return -1;

  sym = str_hash_find (arc_reg_hash, regname);
  if (sym == NULL)
    return -1;

  return S_GET_VALUE (sym);
}

/* Adjust the symbol table.  Delete found AUX register symbols.  */

void arc_adjust_symtab(void)
{
    symbolS *sym = symbol_rootP;
    symbolS *next_sym = NULL;
    
    while (sym != NULL) {
        next_sym = symbol_next(sym);
        
        if ((ARC_GET_FLAG(sym) & ARC_FLAG_AUX) != 0) {
            symbol_remove(sym, &symbol_rootP, &symbol_lastP);
        }
        
        sym = next_sym;
    }
    
    elf_adjust_symtab();
}

static void
tokenize_extinsn (extInstruction_t *einsn)
{
  char *p, c;
  char *insn_name = NULL;
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
    *p = TOLOWER (*p);

  if (*input_line_pointer != ',')
    {
      as_bad (_("expected comma after instruction name"));
      ignore_rest_of_line ();
      free (insn_name);
      return;
    }
  input_line_pointer++;
  major_opcode = get_absolute_expression ();

  SKIP_WHITESPACE ();

  if (*input_line_pointer != ',')
    {
      as_bad (_("expected comma after major opcode"));
      ignore_rest_of_line ();
      free (insn_name);
      return;
    }
  input_line_pointer++;
  sub_opcode = get_absolute_expression ();

  SKIP_WHITESPACE ();

  if (*input_line_pointer != ',')
    {
      as_bad (_("expected comma after sub opcode"));
      ignore_rest_of_line ();
      free (insn_name);
      return;
    }
  input_line_pointer++;

  if (!parse_suffix_class (&suffix_class))
    {
      free (insn_name);
      return;
    }

  if (*input_line_pointer != ',')
    {
      as_bad (_("expected comma after suffix class"));
      ignore_rest_of_line ();
      free (insn_name);
      return;
    }
  input_line_pointer++;

  if (!parse_syntax_classes (&syntax_class, &syntax_class_modifiers))
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
    | ((syntax_class_modifiers & ARC_OP1_IMM_IMPLIED) ? 0x10 : 0);
}

static int
parse_suffix_class (unsigned char *suffix_class)
{
  unsigned int i;
  int found;

  do
    {
      SKIP_WHITESPACE ();
      found = 0;

      for (i = 0; i < ARRAY_SIZE (suffixclass); i++)
        {
          if (!strncmp (suffixclass[i].name, input_line_pointer,
                        suffixclass[i].len))
            {
              *suffix_class |= suffixclass[i].attr_class;
              input_line_pointer += suffixclass[i].len;
              found = 1;
              break;
            }
        }

      if (!found)
        {
          as_bad (_("invalid suffix class"));
          ignore_rest_of_line ();
          return 0;
        }

      SKIP_WHITESPACE ();

      if (*input_line_pointer == '|')
        input_line_pointer++;
      else
        break;
    }
  while (1);

  return 1;
}

static int
parse_syntax_classes (unsigned char *syntax_class,
                      unsigned char *syntax_class_modifiers)
{
  unsigned int i;
  int found;

  do
    {
      SKIP_WHITESPACE ();
      found = 0;

      for (i = 0; i < ARRAY_SIZE (syntaxclassmod); i++)
        {
          if (!strncmp (syntaxclassmod[i].name,
                        input_line_pointer,
                        syntaxclassmod[i].len))
            {
              *syntax_class_modifiers |= syntaxclassmod[i].attr_class;
              input_line_pointer += syntaxclassmod[i].len;
              found = 1;
              break;
            }
        }

      if (!found)
        {
          for (i = 0; i < ARRAY_SIZE (syntaxclass); i++)
            {
              if (!strncmp (syntaxclass[i].name,
                            input_line_pointer,
                            syntaxclass[i].len))
                {
                  *syntax_class |= syntaxclass[i].attr_class;
                  input_line_pointer += syntaxclass[i].len;
                  found = 1;
                  break;
                }
            }
        }

      if (!found)
        {
          as_bad (_("missing syntax class"));
          ignore_rest_of_line ();
          return 0;
        }

      SKIP_WHITESPACE ();

      if (*input_line_pointer == '|')
        input_line_pointer++;
      else
        break;
    }
  while (1);

  return 1;
}

/* Generate an extension section.  */

static int arc_set_ext_seg(void)
{
    if (arcext_section == NULL)
    {
        arcext_section = subseg_new(".arcextmap", 0);
        if (arcext_section == NULL)
        {
            return 0;
        }
        
        if (!bfd_set_section_flags(arcext_section, SEC_READONLY | SEC_HAS_CONTENTS))
        {
            return 0;
        }
    }
    else
    {
        subseg_set(arcext_section, 0);
    }
    
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
  segT old_sec = now_seg;
  int old_subsec = now_subseg;
  char *p;
  size_t name_len;
  
  if (einsn == NULL || einsn->name == NULL) {
    return;
  }
  
  name_len = strlen(einsn->name);
  if (name_len > 249) {
    return;
  }
  
  arc_set_ext_seg();
  
  p = frag_more(1);
  if (p != NULL) {
    *p = (char)(5 + name_len + 1);
  }
  
  p = frag_more(1);
  if (p != NULL) {
    *p = EXT_INSTRUCTION;
  }
  
  p = frag_more(1);
  if (p != NULL) {
    *p = einsn->major;
  }
  
  p = frag_more(1);
  if (p != NULL) {
    *p = einsn->minor;
  }
  
  p = frag_more(1);
  if (p != NULL) {
    *p = einsn->flags;
  }
  
  p = frag_more(name_len + 1);
  if (p != NULL) {
    strncpy(p, einsn->name, name_len);
    p[name_len] = '\0';
  }
  
  subseg_set(old_sec, old_subsec);
}

/* Handler .extinstruction pseudo-op.  */

static void
arc_extinsn (int ignore ATTRIBUTE_UNUSED)
{
  extInstruction_t einsn;
  struct arc_opcode *arc_ext_opcodes;
  const char *errmsg = NULL;
  unsigned char moplow, mophigh;

  memset (&einsn, 0, sizeof (einsn));
  tokenize_extinsn (&einsn);

  if (arc_find_opcode (einsn.name))
    as_warn (_("Pseudocode already used %s"), einsn.name);

  moplow = 0x05;
  mophigh = (selected_cpu.flags & (ARC_OPCODE_ARCv2EM | ARC_OPCODE_ARCv2HS)) ? 0x07 : 0x0a;

  if (einsn.major > mophigh || einsn.major < moplow)
    as_fatal (_("major opcode not in range [0x%02x - 0x%02x]"), moplow, mophigh);

  if (einsn.minor > 0x3f && einsn.major != 0x0a && einsn.major != 5 && einsn.major != 9)
    as_fatal (_("minor opcode not in range [0x00 - 0x3f]"));

  switch (einsn.syntax & ARC_SYNTAX_MASK)
    {
    case ARC_SYNTAX_3OP:
      if (einsn.modsyn & ARC_OP1_IMM_IMPLIED)
        as_fatal (_("Improper use of OP1_IMM_IMPLIED"));
      break;
    case ARC_SYNTAX_2OP:
    case ARC_SYNTAX_1OP:
    case ARC_SYNTAX_NOP:
      if (einsn.modsyn & ARC_OP1_MUST_BE_IMM)
        as_fatal (_("Improper use of OP1_MUST_BE_IMM"));
      break;
    default:
      break;
    }

  arc_ext_opcodes = arcExtMap_genOpcode (&einsn, selected_cpu.flags, &errmsg);
  if (!arc_ext_opcodes)
    {
      if (errmsg)
        as_fatal ("%s", errmsg);
      else
        as_fatal (_("Couldn't generate extension instruction opcodes"));
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
  char c;
  char *p;
  int number;
  int imode = 0;
  bool isCore_p = (opertype == EXT_CORE_REGISTER);
  bool isReg_p = (opertype == EXT_CORE_REGISTER || opertype == EXT_AUX_REGISTER);
  bool success = false;

  SKIP_WHITESPACE ();
  p = input_line_pointer;
  c = get_symbol_name (&p);
  name = xstrdup (p);
  restore_line_pointer (c);

  SKIP_WHITESPACE ();
  if (*input_line_pointer != ',')
    {
      as_bad (_("expected comma after name"));
      goto cleanup;
    }
  input_line_pointer++;
  number = get_absolute_expression ();

  if (number < 0 && opertype != EXT_AUX_REGISTER)
    {
      as_bad (_("%s second argument cannot be a negative number %d"),
              isCore_p ? "extCoreRegister's" : "extCondCode's",
              number);
      goto cleanup;
    }

  if (isReg_p)
    {
      SKIP_WHITESPACE ();
      if (*input_line_pointer != ',')
        {
          as_bad (_("expected comma after register number"));
          goto cleanup;
        }
      input_line_pointer++;

      if (startswith (input_line_pointer, "r|w"))
        {
          imode = 0;
          input_line_pointer += 3;
        }
      else if (startswith (input_line_pointer, "r"))
        {
          imode = ARC_REGISTER_READONLY;
          input_line_pointer += 1;
        }
      else if (startswith (input_line_pointer, "w"))
        {
          imode = ARC_REGISTER_WRITEONLY;
          input_line_pointer += 1;
        }
      else
        {
          as_bad (_("invalid mode"));
          goto cleanup;
        }
    }

  if (isCore_p)
    {
      SKIP_WHITESPACE ();
      if (*input_line_pointer != ',')
        {
          as_bad (_("expected comma after register mode"));
          goto cleanup;
        }
      input_line_pointer++;

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
          goto cleanup;
        }
    }

  demand_empty_rest_of_line ();
  ereg->name = name;
  ereg->number = number;
  ereg->imode = imode;
  return true;

cleanup:
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
  segT old_sec;
  int old_subsec;
  char *p;
  int name_len;
  
  if (ereg == NULL || ereg->name == NULL) {
    return;
  }
  
  name_len = strlen (ereg->name);
  if (name_len > 255) {
    return;
  }
  
  old_sec = now_seg;
  old_subsec = now_subseg;
  
  arc_set_ext_seg ();
  
  if (opertype == EXT_COND_CODE || opertype == EXT_CORE_REGISTER) {
    p = frag_more (1);
    *p = 3 + name_len + 1;
    p = frag_more (1);
    *p = opertype;
    p = frag_more (1);
    *p = ereg->number;
  }
  else if (opertype == EXT_AUX_REGISTER) {
    p = frag_more (1);
    *p = 6 + name_len + 1;
    p = frag_more (1);
    *p = EXT_AUX_REGISTER;
    p = frag_more (1);
    *p = (ereg->number >> 24) & 0xff;
    p = frag_more (1);
    *p = (ereg->number >> 16) & 0xff;
    p = frag_more (1);
    *p = (ereg->number >> 8) & 0xff;
    p = frag_more (1);
    *p = ereg->number & 0xff;
  }
  else {
    subseg_set (old_sec, old_subsec);
    return;
  }
  
  p = frag_more (name_len + 1);
  strncpy (p, ereg->name, name_len);
  p[name_len] = '\0';
  
  subseg_set (old_sec, old_subsec);
}

/* Handler .extCoreRegister pseudo-op.  */

static void
arc_extcorereg (int opertype)
{
  extRegister_t ereg;
  struct arc_aux_reg *auxr;
  struct arc_flag_operand *ccode;

  memset (&ereg, 0, sizeof (ereg));
  if (!tokenize_extregister (&ereg, opertype))
    return;

  switch (opertype)
    {
    case EXT_CORE_REGISTER:
      if (ereg.number > 60)
        {
          as_bad (_("core register %s value (%d) too large"), ereg.name,
                  ereg.number);
          break;
        }
      declare_register (ereg.name, ereg.number);
      break;

    case EXT_AUX_REGISTER:
      auxr = XNEW (struct arc_aux_reg);
      if (auxr == NULL)
        {
          as_bad (_("memory allocation failed"));
          break;
        }
      auxr->name = ereg.name;
      auxr->cpu = selected_cpu.flags;
      auxr->subclass = NONE;
      auxr->address = ereg.number;
      if (str_hash_insert (arc_aux_hash, auxr->name, auxr, 0) != NULL)
        {
          as_bad (_("duplicate aux register %s"), auxr->name);
          free (auxr);
        }
      break;

    case EXT_COND_CODE:
      if (ereg.number > 31)
        {
          as_bad (_("condition code %s value (%d) too large"), ereg.name,
                  ereg.number);
          break;
        }
      ext_condcode.size++;
      ext_condcode.arc_ext_condcode =
        XRESIZEVEC (struct arc_flag_operand, ext_condcode.arc_ext_condcode,
                    ext_condcode.size + 1);
      if (ext_condcode.arc_ext_condcode == NULL)
        {
          as_bad (_("memory allocation failed"));
          ext_condcode.size--;
          break;
        }
      ccode = &ext_condcode.arc_ext_condcode[ext_condcode.size - 1];
      ccode->name   = ereg.name;
      ccode->code   = ereg.number;
      ccode->bits   = 5;
      ccode->shift  = 0;
      ccode->favail = 0;
      memset (&ext_condcode.arc_ext_condcode[ext_condcode.size], 0,
              sizeof (struct arc_flag_operand));
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
    attributes_set_explicitly[tag] = true;
}

/* Set an attribute if it has not already been set by the user.  */

static void
arc_set_attribute_int (int tag, int value)
{
  if (tag < 1 || tag >= NUM_KNOWN_OBJ_ATTRIBUTES)
  {
    if (!bfd_elf_add_proc_attr_int (stdoutput, tag, value))
      as_fatal (_("error adding attribute: %s"),
                bfd_errmsg (bfd_get_error ()));
    return;
  }

  if (!attributes_set_explicitly[tag])
  {
    if (!bfd_elf_add_proc_attr_int (stdoutput, tag, value))
      as_fatal (_("error adding attribute: %s"),
                bfd_errmsg (bfd_get_error ()));
  }
}

static void
arc_set_attribute_string (int tag, const char *value)
{
  if (tag < 1 || tag >= NUM_KNOWN_OBJ_ATTRIBUTES)
  {
    if (!bfd_elf_add_proc_attr_string (stdoutput, tag, value))
      as_fatal (_("error adding attribute: %s"),
                bfd_errmsg (bfd_get_error ()));
    return;
  }

  if (!attributes_set_explicitly[tag])
  {
    if (!bfd_elf_add_proc_attr_string (stdoutput, tag, value))
      as_fatal (_("error adding attribute: %s"),
                bfd_errmsg (bfd_get_error ()));
  }
}

/* Allocate and concatenate two strings.  s1 can be NULL but not
   s2.  s1 pointer is freed at end of this procedure.  */

static char *
arc_stralloc (char * s1, const char * s2)
{
  char * p;
  size_t len1 = 0;
  size_t len2;
  size_t total_len;

  gas_assert (s2);
  
  len2 = strlen (s2);
  
  if (s1)
    {
      len1 = strlen (s1);
      total_len = len1 + len2 + 2;
    }
  else
    {
      total_len = len2 + 1;
    }

  p = xmalloc (total_len);

  if (s1)
    {
      memcpy (p, s1, len1);
      p[len1] = ',';
      memcpy (p + len1 + 1, s2, len2);
      p[len1 + 1 + len2] = '\0';
      free (s1);
    }
  else
    {
      memcpy (p, s2, len2);
      p[len2] = '\0';
    }

  return p;
}

/* Set the public ARC object attributes.  */

static void
arc_set_public_attributes (void)
{
  int base = 0;
  char *s = NULL;
  unsigned int i;

  arc_set_attribute_string (Tag_ARC_CPU_name, selected_cpu.name);

  base = arc_get_cpu_base();
  arc_validate_and_set_cpu_base(base);
  arc_set_osabi_version();
  arc_check_feature();

  for (i = 0; i < ARRAY_SIZE (feature_list); i++)
    if (selected_cpu.features & feature_list[i].feature)
      s = arc_stralloc (s, feature_list[i].attr);

  if (s)
    arc_set_attribute_string (Tag_ARC_ISA_config, s);

  arc_set_attribute_int (Tag_ARC_ISA_mpy_option, mpy_option);
  arc_set_attribute_int (Tag_ARC_ABI_pic, pic_option);
  arc_set_attribute_int (Tag_ARC_ABI_sda, sda_option);
  arc_set_attribute_int (Tag_ARC_ABI_tls, tls_option);
  arc_set_attribute_int (Tag_ARC_ATR_version, 1);

  arc_validate_and_set_rf16();
}

static int
arc_get_cpu_base (void)
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
arc_validate_and_set_cpu_base (int base)
{
  if (attributes_set_explicitly[Tag_ARC_CPU_base])
    {
      int existing_base = bfd_elf_get_obj_attr_int (stdoutput, OBJ_ATTR_PROC,
                                                     Tag_ARC_CPU_base);
      if (base != existing_base)
        as_warn (_("Overwrite explicitly set Tag_ARC_CPU_base"));
    }
  
  if (!bfd_elf_add_proc_attr_int (stdoutput, Tag_ARC_CPU_base, base))
    as_fatal (_("error adding attribute: %s"),
              bfd_errmsg (bfd_get_error ()));
}

static void
arc_set_osabi_version (void)
{
  if (attributes_set_explicitly[Tag_ARC_ABI_osver])
    {
      int val = bfd_elf_get_obj_attr_int (stdoutput, OBJ_ATTR_PROC,
                                           Tag_ARC_ABI_osver);
      selected_cpu.eflags = ((selected_cpu.eflags & ~EF_ARC_OSABI_MSK)
                             | ((val & 0x0f) << 8));
    }
  else
    {
      arc_set_attribute_int (Tag_ARC_ABI_osver, E_ARC_OSABI_CURRENT >> 8);
    }
}

static void
arc_validate_and_set_rf16 (void)
{
  if (!attributes_set_explicitly[Tag_ARC_ABI_rf16])
    return;
    
  int rf16_value = bfd_elf_get_obj_attr_int (stdoutput, OBJ_ATTR_PROC,
                                              Tag_ARC_ABI_rf16);
  if (!rf16_value || rf16_only)
    return;
    
  as_warn (_("Overwrite explicitly set Tag_ARC_ABI_rf16 to full "
             "register file"));
  if (!bfd_elf_add_proc_attr_int (stdoutput, Tag_ARC_ABI_rf16, 0))
    as_fatal (_("error adding attribute: %s"),
              bfd_errmsg (bfd_get_error ()));
}

/* Add the default contents for the .ARC.attributes section.  */

void arc_md_finish(void)
{
    arc_set_public_attributes();

    if (!bfd_set_arch_mach(stdoutput, bfd_arch_arc, selected_cpu.mach)) {
        as_fatal(_("could not set architecture and machine"));
    }

    bfd_set_private_flags(stdoutput, selected_cpu.eflags);
}

void arc_copy_symbol_attributes(symbolS *dest, symbolS *src)
{
  if (dest != NULL && src != NULL)
  {
    ARC_GET_FLAG(dest) = ARC_GET_FLAG(src);
  }
}

int arc_convert_symbolic_attribute(const char *name)
{
  static const struct
  {
    const char *name;
    const int tag;
  }
  attribute_table[] =
  {
    {"Tag_ARC_PCS_config", Tag_ARC_PCS_config},
    {"Tag_ARC_CPU_base", Tag_ARC_CPU_base},
    {"Tag_ARC_CPU_variation", Tag_ARC_CPU_variation},
    {"Tag_ARC_CPU_name", Tag_ARC_CPU_name},
    {"Tag_ARC_ABI_rf16", Tag_ARC_ABI_rf16},
    {"Tag_ARC_ABI_osver", Tag_ARC_ABI_osver},
    {"Tag_ARC_ABI_sda", Tag_ARC_ABI_sda},
    {"Tag_ARC_ABI_pic", Tag_ARC_ABI_pic},
    {"Tag_ARC_ABI_tls", Tag_ARC_ABI_tls},
    {"Tag_ARC_ABI_enumsize", Tag_ARC_ABI_enumsize},
    {"Tag_ARC_ABI_exceptions", Tag_ARC_ABI_exceptions},
    {"Tag_ARC_ABI_double_size", Tag_ARC_ABI_double_size},
    {"Tag_ARC_ISA_config", Tag_ARC_ISA_config},
    {"Tag_ARC_ISA_apex", Tag_ARC_ISA_apex},
    {"Tag_ARC_ISA_mpy_option", Tag_ARC_ISA_mpy_option},
    {"Tag_ARC_ATR_version", Tag_ARC_ATR_version}
  };

  if (name == NULL)
    return -1;

  for (unsigned int i = 0; i < ARRAY_SIZE(attribute_table); i++)
    if (streq(name, attribute_table[i].name))
      return attribute_table[i].tag;

  return -1;
}

/* Local variables:
   eval: (c-set-style "gnu")
   indent-tabs-mode: t
   End:  */
