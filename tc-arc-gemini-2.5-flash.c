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
  if (name == NULL) {
    return NULL;
  }
  return str_hash_find (arc_opcode_hash, name);
}

/* Initialise the iterator ITER.  */

static void
arc_opcode_hash_entry_iterator_init (struct arc_opcode_hash_entry_iterator *iter)
{
  assert(iter != NULL);
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
  if (entry == NULL || iter == NULL)
    return NULL;

  const struct arc_opcode *current_return_opcode = iter->opcode;

  if (current_return_opcode == NULL)
    {
      /* This is the first call for this iterator or iteration was already exhausted. */
      if (iter->index == 0)
	{
	  /* Truly the first call. Initialize the iterator. */
	  gas_assert (entry->count > 0); /* Precondition: entry must have opcodes. */
	  if (entry->count == 0)
	    return NULL; /* If assert is disabled, handle empty entry gracefully. */

	  iter->opcode = entry->opcode[0]; /* Set the first opcode for this call. */
	  iter->index = 0; /* Keep index aligned with the current group start. */
	}
      /* If iter->opcode is NULL and iter->index != 0, it means iteration was
	 exhausted on a previous call and iter->opcode was set to NULL. */
    }
  else /* Not the first call; current_return_opcode holds the previously returned value. */
    {
      const char *old_name = current_return_opcode->name;

      /* Calculate the next physical opcode candidate. */
      /* First, determine the physical index of the current opcode to prevent out-of-bounds access. */
      ptrdiff_t current_physical_idx = current_return_opcode - entry->opcode;

      /* If we are at or past the last element in the physical array, the next one is NULL. */
      if (current_physical_idx >= entry->count - 1)
	{
	  iter->opcode = NULL;
	  /* Align iter->index to indicate exhaustion, but don't blindly assign entry->count
	     if iter->index has a different meaning (group start). The original code uses
	     iter->index == entry->count as exhaustion marker. */
	  if (iter->index < entry->count)
	    iter->index = entry->count; /* Ensure iter->index is also past end. */
	}
      else
	{
	  const struct arc_opcode *next_physical_candidate = current_return_opcode + 1;

	  /* Original logic: check name change OR if next_physical_candidate->name is NULL.
	     The name==NULL check likely signifies a sentinel or an error, but it's part of original behavior. */
	  if (next_physical_candidate->name == NULL || strcmp (old_name, next_physical_candidate->name) != 0)
	    {
	      /* Name changed (new group) or sentinel reached. Advance group index. */
	      iter->index++;

	      if (iter->index >= entry->count)
		{
		  /* New group index is past the end of the entry's array. */
		  iter->opcode = NULL;
		}
	      else
		{
		  /* Reset the current opcode pointer to the start of the new group. */
		  iter->opcode = entry->opcode[iter->index];
		}
	    }
	  else
	    {
	      /* Name matches, continue iterating within the same group.
		 iter->opcode simply advances physically; iter->index (group start) does not change. */
	      iter->opcode = next_physical_candidate;
	    }
	}
    }

  /* The value returned is the iter->opcode *before* the state update
     (unless it was the first initialization), as per the original function's structure. */
  return current_return_opcode;
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
          as_fatal (_("duplicate %s"), name);
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

  string_tuple_t *tuple = (string_tuple_t *)elt;

  if (tuple->value != NULL)
  {
    struct arc_opcode_hash_entry *entry = (struct arc_opcode_hash_entry *)tuple->value;
    free (entry->opcode);
    free (entry);
  }

  free (tuple);
}

/* Like md_number_to_chars but for middle-endian values.  The 4-byte limm
   value, is encoded as 'middle-endian' for a little-endian target.  This
   function is used for regular 4, 6, and 8 byte instructions as well.  */

#include <stdlib.h>

extern void md_number_to_chars(char *buf, unsigned long long val, int n);

static void
md_number_to_chars_midend (char *buf, unsigned long long val, int n)
{
  if (buf == NULL) {
    abort();
  }

  switch (n)
    {
    case 2:
      md_number_to_chars(buf, val, 2);
      break;
    case 4:
      md_number_to_chars(buf, (val >> 16) & 0xFFFFull, 2);
      md_number_to_chars(buf + 2, val & 0xFFFFull, 2);
      break;
    case 6:
      md_number_to_chars(buf, (val >> 32) & 0xFFFFull, 2);
      md_number_to_chars_midend(buf + 2, val & 0xFFFFFFFFull, 4);
      break;
    case 8:
      md_number_to_chars_midend(buf, (val >> 32) & 0xFFFFFFFFull, 4);
      md_number_to_chars_midend(buf + 4, val & 0xFFFFFFFFull, 4);
      break;
    default:
      abort();
    }
}

/* Check if a feature is allowed for a specific CPU.  */

static int is_feature_invalid_for_cpu(unsigned int feature_index) {
  const struct feature_info *feature = &feature_list[feature_index];
  int feature_is_enabled_in_cpu_config = (selected_cpu.features & feature->feature) != 0;
  int cpu_lacks_required_flags_for_feature = (selected_cpu.flags & feature->cpus) == 0;

  return feature_is_enabled_in_cpu_config && cpu_lacks_required_flags_for_feature;
}

static int has_conflicting_isa_extensions(unsigned int conflict_index) {
  unsigned int conflict_mask = conflict_list[conflict_index];
  return (selected_cpu.features & conflict_mask) == conflict_mask;
}

static void
arc_check_feature (void)
{
  if (!selected_cpu.features || !selected_cpu.name) {
    return;
  }

  for (unsigned int i = 0; i < ARRAY_SIZE (feature_list); ++i) {
    if (is_feature_invalid_for_cpu(i)) {
      as_bad(_("invalid %s option for %s cpu"), feature_list[i].name,
             selected_cpu.name);
    }
  }

  for (unsigned int i = 0; i < ARRAY_SIZE (conflict_list); ++i) {
    if (has_conflicting_isa_extensions(i)) {
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
  struct cpu_type *found_cpu = NULL;
  static struct cpu_type old_cpu = { 0, 0, 0, E_ARC_OSABI_CURRENT, 0 };

  gas_assert (sel != MACH_SELECTION_FROM_DEFAULT
              || mach_selection_mode == MACH_SELECTION_NONE);

  if ((mach_selection_mode == MACH_SELECTION_FROM_CPU_DIRECTIVE)
      && (sel == MACH_SELECTION_FROM_CPU_DIRECTIVE))
    {
      as_bad (_("Multiple .cpu directives found"));
    }

  for (int i = 0; cpu_types[i].name; ++i)
    {
      if (!strcasecmp (cpu_types[i].name, arg))
        {
          found_cpu = &cpu_types[i];
          break;
        }
    }

  if (found_cpu == NULL)
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
          return;
        }
    }

  selected_cpu.flags = found_cpu->flags;
  selected_cpu.name = found_cpu->name;
  selected_cpu.features = found_cpu->features | cl_features;
  selected_cpu.mach = found_cpu->mach;
  selected_cpu.eflags = ((selected_cpu.eflags & ~EF_ARC_MACH_MSK)
                         | found_cpu->eflags);

  arc_check_feature ();

  if (mach_selection_mode != MACH_SELECTION_NONE
      && (old_cpu.mach != selected_cpu.mach))
    {
      bfd_find_target (arc_target_format, stdoutput);
      if (! bfd_set_arch_mach (stdoutput, bfd_arch_arc, selected_cpu.mach))
        {
          as_warn (_("Could not set architecture and machine"));
        }
    }

  mach_selection_mode = sel;
  old_cpu = selected_cpu;
}

/* Here ends all the ARCompact extension instruction assembling
   stuff.  */

static void
arc_extra_reloc (int r_type)
{
  symbolS *main_symbol = NULL;
  symbolS *sub_symbol = NULL;

  if (*input_line_pointer == '@')
    input_line_pointer++;

  char *current_symbol_name;
  char char_after_first_symbol = get_symbol_name (&current_symbol_name);
  main_symbol = symbol_find_or_make (current_symbol_name);
  restore_line_pointer (char_after_first_symbol);

  if (char_after_first_symbol == ',' && r_type == BFD_RELOC_ARC_TLS_GD_LD)
    {
      ++input_line_pointer;

      char *secondary_symbol_name;
      char char_after_second_symbol = get_symbol_name (&secondary_symbol_name);
      sub_symbol = symbol_find_or_make (secondary_symbol_name);
      restore_line_pointer (char_after_second_symbol);
    }

  fixS *new_fix
    = fix_new (frag_now,
	       frag_now_fix (),
	       0,
	       main_symbol,
	       0,
	       false,
	       r_type);

  new_fix->fx_subsy = sub_symbol;
}

static symbolS *
arc_lcomm_internal (int ignore ATTRIBUTE_UNUSED,
		    symbolS *symbolP, addressT size)
{
  addressT align = 0;

  SKIP_WHITESPACE ();

  if (*input_line_pointer == ',')
    {
      align = parse_align (1);

      if (align == (addressT) -1)
        {
	  return NULL;
        }
    }
  else
    {
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
      struct bfd_symbol *bfd_sym_ptr = symbol_get_bfdsym(symbolP);
      if (bfd_sym_ptr != NULL)
        {
          bfd_sym_ptr->flags |= BSF_OBJECT;
        }
    }
}

/* Select the cpu we're assembling for.  */

typedef struct {
    const char *alias;
    const char *canonical_name;
} cpu_alias_map_t;

static const cpu_alias_map_t cpu_aliases[] = {
    {"ARC600", "arc600"},
    {"ARC601", "arc600"},
    {"A6",     "arc600"},
    {"ARC700", "arc700"},
    {"A7",     "arc700"},
    {"EM",     "arcem"},
    {"HS",     "archs"},
    {"NPS400", "nps400"},
    {NULL,     NULL}
};

static void
arc_option (int ignore ATTRIBUTE_UNUSED)
{
  char c;
  char *cpu_input_name;
  const char *selected_cpu_name;

  c = get_symbol_name (&cpu_input_name);

  selected_cpu_name = cpu_input_name;

  if (cpu_input_name != NULL) {
      for (int i = 0; cpu_aliases[i].alias != NULL; ++i) {
          if (!strcmp(cpu_aliases[i].alias, cpu_input_name)) {
              selected_cpu_name = cpu_aliases[i].canonical_name;
              break;
          }
      }
  }

  arc_select_cpu (selected_cpu_name, MACH_SELECTION_FROM_CPU_DIRECTIVE);

  restore_line_pointer (c);
  demand_empty_rest_of_line ();
}

/* Smartly print an expression.  */

static const char *get_expression_op_name(int op_code)
{
  switch (op_code)
    {
    case O_illegal:		return "O_illegal";
    case O_absent:		return "O_absent";
    case O_constant:		return "O_constant";
    case O_symbol:		return "O_symbol";
    case O_symbol_rva:		return "O_symbol_rva";
    case O_register:		return "O_register";
    case O_big:			return "O_big";
    case O_uminus:		return "O_uminus";
    case O_bit_not:		return "O_bit_not";
    case O_logical_not:		return "O_logical_not";
    case O_multiply:		return "O_multiply";
    case O_divide:		return "O_divide";
    case O_modulus:		return "O_modulus";
    case O_left_shift:		return "O_left_shift";
    case O_right_shift:		return "O_right_shift";
    case O_bit_inclusive_or:	return "O_bit_inclusive_or";
    case O_bit_or_not:		return "O_bit_or_not";
    case O_bit_exclusive_or:	return "O_bit_exclusive_or";
    case O_bit_and:		return "O_bit_and";
    case O_add:			return "O_add";
    case O_subtract:		return "O_subtract";
    case O_eq:			return "O_eq";
    case O_ne:			return "O_ne";
    case O_lt:			return "O_lt";
    case O_le:			return "O_le";
    case O_ge:			return "O_ge";
    case O_gt:			return "O_gt";
    case O_logical_and:		return "O_logical_and";
    case O_logical_or:		return "O_logical_or";
    case O_index:		return "O_index";
    case O_bracket:		return "O_bracket";
    case O_colon:		return "O_colon";
    case O_addrtype:		return "O_addrtype";
    default:			return "unknown";
    }
}

static const char *get_expression_md_name(int md_code)
{
  switch (md_code)
    {
    case O_gotoff:		return "O_gotoff";
    case O_gotpc:		return "O_gotpc";
    case O_plt:			return "O_plt";
    case O_sda:			return "O_sda";
    case O_pcl:			return "O_pcl";
    case O_tlsgd:		return "O_tlsgd";
    case O_tlsie:		return "O_tlsie";
    case O_tpoff9:		return "O_tpoff9";
    case O_tpoff:		return "O_tpoff";
    case O_dtpoff9:		return "O_dtpoff9";
    case O_dtpoff:		return "O_dtpoff";
    default:			return "unknown";
    }
}

static void
debug_exp (expressionS *t)
{
  if (t == NULL)
    {
      pr_debug ("debug_exp: NULL expressionS pointer provided.\n");
      fflush (stderr);
      return;
    }

  const char *name = get_expression_op_name(t->X_op);
  const char *namemd_raw = get_expression_md_name(t->X_md);
  const char *namemd = (t->X_md) ? namemd_raw : "--";

  pr_debug ("debug_exp: %s (%s, %s, %d, %s)\n", name,
	    (t->X_add_symbol) ? S_GET_NAME (t->X_add_symbol) : "--",
	    (t->X_op_symbol) ? S_GET_NAME (t->X_op_symbol) : "--",
	    (int) t->X_add_number,
	    namemd);
  fflush (stderr);
}

/* Helper for parsing an argument, used for sorting out the relocation
   type.  */

static void
parse_reloc_symbol (expressionS *resultP)
{
  char *reloc_name = NULL;
  char *sym_name = NULL;
  char c;
  size_t len;
  const struct arc_reloc_op_tag *r = NULL;
  expressionS right;
  symbolS *base = NULL;

  /* Initialize right.X_add_number. It will be overwritten if a constant expression is found,
     otherwise it defaults to 0. */
  right.X_add_number = 0;

  /* A relocation operand has the following form @identifier@relocation_type.
     The identifier is already in tok!  */
  if (resultP->X_op != O_symbol)
    {
      as_bad (_("No valid label relocation operand"));
      resultP->X_op = O_illegal;
      return;
    }

  /* Parse @relocation_type.  */
  input_line_pointer++; /* Skip the leading '@' for relocation type */
  c = get_symbol_name (&reloc_name);
  len = input_line_pointer - reloc_name;

  if (len == 0)
    {
      as_bad (_("No relocation operand"));
      resultP->X_op = O_illegal;
      return;
    }

  /* Go through known relocation and try to find a match.  */
  const struct arc_reloc_op_tag *found_reloc_op = NULL;
  for (int i = 0; i < arc_num_reloc_op; ++i)
    {
      if (len == arc_reloc_op[i].length && memcmp (reloc_name, arc_reloc_op[i].name, len) == 0)
        {
          found_reloc_op = &arc_reloc_op[i];
          break;
        }
    }

  if (found_reloc_op == NULL)
    {
      as_bad (_("Unknown relocation operand: @%s"), reloc_name);
      resultP->X_op = O_illegal;
      return;
    }
  r = found_reloc_op;

  restore_line_pointer (c); /* Restore pointer after '@relocation_type' token */
  SKIP_WHITESPACE ();

  /* Extra check for TLS: base (e.g., @sym@TLSGD@base).  */
  if (*input_line_pointer == '@')
    {
      /* If resultP already contains a symbol, it's an error when parsing a TLS base.
         The condition 'resultP->X_op != O_symbol' is redundant here as it's
         guaranteed to be O_symbol by the first check in this function. */
      if (resultP->X_op_symbol != NULL)
        {
          as_bad (_("Unable to parse TLS base: %s"), input_line_pointer);
          resultP->X_op = O_illegal;
          return;
        }

      input_line_pointer++; /* Skip the leading '@' for TLS base */
      c = get_symbol_name (&sym_name);
      base = symbol_find_or_make (sym_name);
      resultP->X_op = O_subtract; /* This implies the expression is 'base - offset' */
      resultP->X_op_symbol = base;
      restore_line_pointer (c); /* Restore pointer after '@base' token */
      SKIP_WHITESPACE ();
    }

  /* Parse the constant of a complex relocation expression like @identifier@reloc +/- const.  */
  if ((*input_line_pointer == '+') || (*input_line_pointer == '-'))
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
          as_bad (_("Bad expression: @%s %s."), r->name, input_line_pointer);
          resultP->X_op = O_illegal;
          return;
        }
    }
  /* If no '+' or '-' is found, right.X_add_number remains 0 (from initial assignment),
     which is the correct behavior for no explicit offset. */

  resultP->X_md = r->op;
  resultP->X_add_number = right.X_add_number;
}

/* Parse the arguments to an opcode.  */

static int
tokenize_arguments (char *str,
		    expressionS *tok_start,
		    int ntok)
{
  char *old_input_line_pointer = input_line_pointer;
  input_line_pointer = str;

  bool saw_comma = false;
  bool saw_arg = false;
  int brk_lvl = 0;
  int num_args = 0;
  expressionS *current_tok = tok_start;

  memset (tok_start, 0, sizeof (*tok_start) * ntok);

  int ret_val = -1; /* Default to error */
  bool parse_success = true;

  while (*input_line_pointer != '\0' && parse_success)
    {
      SKIP_WHITESPACE ();
      char c = *input_line_pointer;

      if (c == '\0')
        break; /* End of string after skipping whitespace */

      /* Check for buffer overflow before attempting to process a new token,
         as each successful token processing increments num_args. */
      if (num_args >= ntok) {
          as_bad (_("Too many arguments or tokens provided"));
          parse_success = false;
          break;
      }

      switch (c)
	{
	case ',':
	  input_line_pointer++;
	  if (saw_comma || !saw_arg || brk_lvl > 0) {
	    as_bad (_("Invalid comma usage"));
	    parse_success = false;
	  } else {
	    saw_comma = true;
	    saw_arg = false;
	  }
	  break;

	case '}':
	case ']':
	  input_line_pointer++;
	  --brk_lvl;
	  if (!saw_arg || brk_lvl < 0) {
	    as_bad (_("Brackets in operand field incorrect"));
	    parse_success = false;
	  } else {
	    current_tok->X_op = O_bracket;
	    current_tok++;
	    num_args++;
	    saw_comma = false;
	    saw_arg = true;
	  }
	  break;

	case '{':
	case '[':
	  input_line_pointer++;
	  if (brk_lvl > 0 || saw_arg) {
	    as_bad (_("Invalid bracket usage or missing comma"));
	    parse_success = false;
	  } else {
	    ++brk_lvl;
	    current_tok->X_op = O_bracket;
	    current_tok++;
	    num_args++;
	    saw_comma = false;
	    saw_arg = true;
	  }
	  break;

    case ':':
          input_line_pointer++;
          if (!saw_arg || saw_comma || brk_lvl > 0) {
            as_bad(_("Invalid colon usage"));
            parse_success = false;
          } else {
            current_tok->X_op = O_colon;
            current_tok++;
            num_args++;
            saw_comma = false;
            saw_arg = false; /* Colon implies next token is a new arg */
          }
          break;

	case '@':
	case '%':
	default:
	  if (saw_arg && !saw_comma) {
	    as_bad (_("Missing comma or colon"));
	    parse_success = false;
	    break; /* Break from switch to terminate loop */
	  }
          if (brk_lvl < 0) {
             as_bad (_("Brackets in operand field incorrect"));
             parse_success = false;
             break;
          }

          /* Parse the actual expression */
          bool is_at_symbol = false;
          if (c == '@') {
            input_line_pointer++;
            is_at_symbol = true;
          } else if (c == '%') {
            input_line_pointer++;
          }

          /* Initialize expression struct fields before calling expression() */
          current_tok->X_op = O_absent;
          current_tok->X_md = O_absent;

          if (is_at_symbol) {
              current_tok->X_op = O_symbol; /* Specific for @ */
              expression (current_tok);
              if (*input_line_pointer == '@')
                parse_reloc_symbol (current_tok);
          } else { /* % or default */
              expression (current_tok);
              if (*input_line_pointer == '@')
                parse_reloc_symbol (current_tok);
              else
                resolve_register (current_tok);
          }

          debug_exp (current_tok);

          if (current_tok->X_op == O_illegal || current_tok->X_op == O_absent) {
            as_bad (_("Illegal or missing expression"));
            parse_success = false;
            break;
          }

          saw_comma = false;
          saw_arg = true;
          current_tok++;
          num_args++;
          break;
	}
    }

  if (parse_success) { /* Final checks only if no errors during the loop */
    if (saw_comma) {
      as_bad (_("Extra comma at end of arguments"));
      parse_success = false;
    }
    if (brk_lvl > 0) {
      as_bad (_("Unmatched opening bracket"));
      parse_success = false;
    }
    if (brk_lvl < 0) { /* Defensive check, should be caught in loop */
        as_bad (_("Unmatched closing bracket"));
        parse_success = false;
    }
  }

  input_line_pointer = old_input_line_pointer; /* Always restore global pointer */

  if (parse_success) {
    ret_val = num_args;
  } else {
    ret_val = -1;
  }

  return ret_val;
}

/* Parse the flags to a structure.  */

static int
tokenize_flags (const char *str,
		struct arc_flags flags[],
		int nflg)
{
  char *old_global_input_line_pointer;
  char *current_pos = (char *) str;
  bool saw_flg = false;
  bool saw_dot = false;
  int num_flags  = 0;
  size_t flgnamelen;
  int parse_status = 0; // 0 for ongoing/success, -1 for error

  memset (flags, 0, sizeof (*flags) * nflg);

  // Save the global input_line_pointer to restore it later.
  // This function uses `current_pos` as its local parsing cursor for `str`.
  old_global_input_line_pointer = input_line_pointer;

  while (*current_pos)
    {
      if (is_end_of_stmt (*current_pos) || is_whitespace (*current_pos))
        {
          // Encountered end of statement or whitespace,
          // which signifies the end of the flag list for this parsing context.
          break; // Normal termination of flag parsing
        }

      switch (*current_pos)
	{
	case '.':
	  current_pos++;
	  if (saw_dot)
	    {
	      as_bad (_("extra dot"));
	      parse_status = -1;
	    }
	  saw_dot = true;
	  saw_flg = false; // A dot resets the "saw a flag" state for the next token.
	  break;

	default:
	  // If we've seen a flag but not a separating dot, and now encounter another non-dot character, it's a format error.
	  // Example: "flag1flag2" (missing dot between flags).
	  if (saw_flg && !saw_dot)
	    {
	      as_bad (_("missing dot separator between flags"));
	      parse_status = -1;
	    }
	  // Check if there's space in the flags array.
	  else if (num_flags >= nflg)
	    {
	      as_bad (_("too many flags specified (buffer exhausted)"));
	      parse_status = -1;
	    }
	  else
	    {
	      // Attempt to parse a flag name.
	      flgnamelen = strspn (current_pos,
				   "abcdefghijklmnopqrstuvwxyz0123456789");

	      if (flgnamelen == 0) // The current character is not part of a valid flag name.
		{
		  as_bad (_("unrecognized character in flag name or malformed flag"));
		  parse_status = -1;
		}
	      // Check if the flag name is too long for the buffer.
	      // MAX_FLAG_NAME_LENGTH is assumed to be the maximum *content* length,
	      // implying `flags->name` buffer has space for `MAX_FLAG_NAME_LENGTH + 1` bytes (for null terminator).
	      else if (flgnamelen > MAX_FLAG_NAME_LENGTH)
		{
		  as_bad (_("flag name exceeds maximum allowed length"));
		  parse_status = -1;
		}
	      else
		{
		  // Copy the flag name into the structure.
		  // The previous check ensures `flgnamelen` will fit within `MAX_FLAG_NAME_LENGTH`.
		  // We assume `flags->name` is `char[MAX_FLAG_NAME_LENGTH + 1]` or larger.
		  memcpy (flags->name, current_pos, flgnamelen);
		  flags->name[flgnamelen] = '\0'; // Always null-terminate for robustness and SonarCloud compliance.

		  current_pos += flgnamelen; // Advance cursor past the flag name.
		  flags++; // Move to the next `struct arc_flags` in the array.
		  saw_dot = false; // After a flag, a dot is expected before the next flag (if any).
		  saw_flg = true;  // We have successfully processed a flag.
		  num_flags++;
		}
	    }
	  break;
	} // end switch

      // If an error was detected in the current iteration, break out of the loop.
      if (parse_status == -1)
        {
          break;
        }
    } // end while

  // Restore the global input_line_pointer to its original value.
  input_line_pointer = old_global_input_line_pointer;

  if (parse_status == -1) {
    return -1; // An error occurred during parsing.
  }
  return num_flags; // Success: return the number of flags successfully parsed.
}

/* Apply the fixups in order.  */

static void
apply_fixups (struct arc_insn *insn, fragS *fragP, int fix)
{
  int i;

  for (i = 0; i < insn->nfixups; i++)
    {
      struct arc_fixup *fixup = &insn->fixups[i];
      int size, pcrel, offset = 0;

      size = ((insn->len == 2) && !fixup->islong) ? 2 : 4;

      if (fixup->islong)
	offset = insn->len;

      if (fixup->reloc == 0)
	as_fatal (_("Unhandled reloc type"));

      if ((int) fixup->reloc < 0)
	{
	  pcrel = fixup->pcrel;
	}
      else
	{
	  reloc_howto_type *reloc_howto =
	    bfd_reloc_type_lookup (stdoutput, fixup->reloc);

	  if (!reloc_howto)
	    as_fatal (_("Failed to lookup BFD relocation type %d"), fixup->reloc);

	  pcrel = reloc_howto->pc_relative;
	}

      pr_debug ("%s:%d: apply_fixups: new %s fixup (PCrel:%s) of size %d @ "
		"offset %d + %d\n",
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
  char *f;
  size_t total_len;
  const int LONG_IMM_SIZE = 4;

  if (insn == NULL) {
    return;
  }

  if (relax && where == NULL) {
    return;
  }

  pr_debug ("Emit insn : 0x%llx\n", insn->insn);
  pr_debug ("\tLength  : %d\n", insn->len);
  pr_debug ("\tLong imm: 0x%lx\n", insn->limm);

  total_len = insn->len + (insn->has_limm ? LONG_IMM_SIZE : 0);

  if (!relax) {
    f = frag_more (total_len);
    if (f == NULL) {
      return;
    }
  } else {
    f = where;
  }

  md_number_to_chars_midend(f, insn->insn, insn->len);

  if (insn->has_limm) {
    md_number_to_chars_midend (f + insn->len, insn->limm, LONG_IMM_SIZE);
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

  relax_substateT subtype_for_frag_var;

  if (frag_room () < FRAG_MAX_GROWTH)
    {
      struct arc_relax_type preserved_tc_data;
      relax_substateT preserved_subtype;

      memcpy (&preserved_tc_data, &frag_now->tc_frag_data,
              sizeof (struct arc_relax_type));
      preserved_subtype = frag_now->fr_subtype;

      frag_wane (frag_now);
      frag_grow (FRAG_MAX_GROWTH);

      memcpy (&frag_now->tc_frag_data, &preserved_tc_data,
              sizeof (struct arc_relax_type));

      subtype_for_frag_var = preserved_subtype;
    }
  else
    {
      subtype_for_frag_var = frag_now->fr_subtype;
    }

  frag_var (rs_machine_dependent, FRAG_MAX_GROWTH, 0,
            subtype_for_frag_var, s, 0, 0);
}

static void
emit_insn (struct arc_insn *insn)
{
  if (insn == NULL)
    {
      return;
    }

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
    {
      return false;
    }

  expressionS *ex = symbol_get_value_expression (sym);

  if (!ex)
    {
      return false;
    }

  if (O_register != ex->X_op)
    {
      return false;
    }

  if (contains_register (ex->X_add_symbol))
    {
      return false;
    }

  if (contains_register (ex->X_op_symbol))
    {
      return false;
    }

  return true;
}

/* Returns the register number within a symbol.  */

static int
get_register (symbolS *sym)
{
  if (sym == NULL) {
    return -1;
  }

  if (!contains_register (sym)) {
    return -1;
  }

  expressionS *ex = symbol_get_value_expression (sym);

  if (ex == NULL) {
    return -1;
  }

  return regno (ex->X_add_number);
}

/* Return true if a RELOC is generic.  A generic reloc is PC-rel of a
   simple ME relocation (e.g. RELOC_ARC_32_ME, BFD_RELOC_ARC_PC32.  */

static bool
generic_reloc_p (extended_bfd_reloc_code_real_type reloc)
{
  if (reloc == 0)
    return false;

  switch (reloc)
    {
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
  if (ntok >= MAX_INSN_ARGS - 1)
    return 0; /* No space left.  */

  if (cidx < 0 || cidx > ntok)
    return 0; /* Incorrect args.  */

  size_t num_elements_to_shift = (size_t)(ntok - cidx + 1);
  memmove(&tok[cidx + 1], &tok[cidx], num_elements_to_shift * sizeof(expressionS));

  return 1; /* Success.  */
}

/* Check if an particular ARC feature is enabled.  */

static bool
check_cpu_feature (insn_subclass_t sc)
{
  return !(
      (is_code_density_p (sc) && !(selected_cpu.features & CD)) ||
      (is_spfp_p (sc) && !(selected_cpu.features & SPX)) ||
      (is_dpfp_p (sc) && !(selected_cpu.features & DPX)) ||
      (is_fpuda_p (sc) && !(selected_cpu.features & DPA)) ||
      (is_nps400_p (sc) && !(selected_cpu.features & NPS400))
  );
}

/* Parse the flags described by FIRST_PFLAG and NFLGS against the flag
   operands in OPCODE.  Stores the matching OPCODES into the FIRST_PFLAG
   array and returns TRUE if the flag operands all match, otherwise,
   returns FALSE, in which case the FIRST_PFLAG array may have been
   modified.  */

static struct arc_flags*
find_parsed_flag_by_name_internal(const char *name, struct arc_flags *first_pflag, int nflgs)
{
    for (int i = 0; i < nflgs; i++)
    {
        if (!strcmp(name, first_pflag[i].name))
        {
            return &first_pflag[i];
        }
    }
    return NULL;
}

static bool
parse_opcode_flags (const struct arc_opcode *opcode,
                    int nflgs,
                    struct arc_flags *first_pflag)
{
  int unmatched_parsed_flags_count = nflgs;

  for (int i = 0; i < nflgs; i++)
    first_pflag[i].flgp = NULL;

  for (const unsigned char *flgidx = opcode->flags; *flgidx; ++flgidx)
    {
      const struct arc_flag_class *cl_flags = &arc_flag_classes[*flgidx];
      int cl_matches_count = 0;

      if (cl_flags->flag_class & F_CLASS_IMPLICIT)
	    continue;

      if (ext_condcode.arc_ext_condcode && (cl_flags->flag_class & F_CLASS_EXTEND))
        {
          for (const struct arc_flag_operand *pf = ext_condcode.arc_ext_condcode; pf->name; ++pf)
            {
              struct arc_flags *pflag_match = find_parsed_flag_by_name_internal(pf->name, first_pflag, nflgs);
              if (pflag_match != NULL)
                {
                  if (pflag_match->flgp != NULL)
                    return false;
                  
                  pflag_match->flgp = pf;
                  unmatched_parsed_flags_count--;
                  cl_matches_count++;
                }
            }
        }

      for (const unsigned *flgopridx = cl_flags->flags; *flgopridx; ++flgopridx)
        {
          const struct arc_flag_operand *flg_operand = &arc_flag_operands[*flgopridx];
          
          struct arc_flags *pflag_match = find_parsed_flag_by_name_internal(flg_operand->name, first_pflag, nflgs);
          if (pflag_match != NULL)
            {
              if (pflag_match->flgp != NULL)
                return false;
              
              pflag_match->flgp = flg_operand;
              unmatched_parsed_flags_count--;
              cl_matches_count++;
            }
        }

      if ((cl_flags->flag_class & F_CLASS_REQUIRED) && cl_matches_count == 0)
        return false;
      if ((cl_flags->flag_class & F_CLASS_OPTIONAL) && cl_matches_count > 1)
        return false;
    }

  return unmatched_parsed_flags_count == 0;
}


/* Search forward through all variants of an opcode looking for a
   syntax match.  */

static bool check_operand_addrtype_logic(const struct arc_operand *operand,
                                         const expressionS *token,
                                         const char **errmsg_out);
static bool check_operand_ir_logic(const struct arc_operand *operand,
                                   expressionS *token_base_ptr,
                                   int token_idx,
                                   int *p_current_ntok,
                                   const expressionS *prev_token,
                                   const char **errmsg_out);
static bool handle_numeric_operand_logic(const struct arc_opcode *opcode,
                                         const struct arc_operand *operand,
                                         expressionS *token_base_ptr,
                                         int token_idx,
                                         int *p_current_ntok,
                                         const expressionS *prev_token,
                                         const char **errmsg_out);

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
  int initial_ntok = *pntok;
  int got_cpu_match = 0;
  expressionS bktok[MAX_INSN_ARGS];
  int bkntok;
  int max_error_idx = 0;
  const char *best_errmsg = NULL;

  arc_opcode_hash_entry_iterator_init (&iter);

  memcpy (bktok, tok, MAX_INSN_ARGS * sizeof (*tok));
  bkntok = initial_ntok;

  for (opcode = arc_opcode_hash_entry_iterator_next (entry, &iter);
       opcode != NULL;
       opcode = arc_opcode_hash_entry_iterator_next (entry, &iter))
    {
      bool current_opcode_match_failed = false;
      const char *current_errmsg = NULL;
      int current_ntok = initial_ntok;

      memcpy(tok, bktok, MAX_INSN_ARGS * sizeof(*tok));

      if (!(opcode->cpu & selected_cpu.flags)) {
        current_opcode_match_failed = true;
      } else if (!check_cpu_feature(opcode->subclass)) {
        current_opcode_match_failed = true;
      }

      if (current_opcode_match_failed) {
        continue;
      }

      got_cpu_match = 1;

      int tokidx = 0;
      const expressionS *prev_tok = NULL;

      for (const unsigned char *opidx_ptr = opcode->operands; *opidx_ptr; ++opidx_ptr)
	    {
	      const struct arc_operand *operand = &arc_operands[*opidx_ptr];

	      if (ARC_OPERAND_IS_FAKE (operand)) {
	        continue;
          }

          if (tokidx >= current_ntok) {
            current_errmsg = _("missing operand");
            current_opcode_match_failed = true;
            break;
          }

          const char *operand_specific_errmsg = NULL;

          switch (operand->flags & ARC_OPERAND_TYPECHECK_MASK)
            {
            case ARC_OPERAND_ADDRTYPE:
              if (!check_operand_addrtype_logic(operand, &tok[tokidx], &operand_specific_errmsg)) {
                current_opcode_match_failed = true;
              }
              break;

            case ARC_OPERAND_IR:
              if (!check_operand_ir_logic(operand, tok, tokidx, &current_ntok, prev_tok, &operand_specific_errmsg)) {
                current_opcode_match_failed = true;
              }
              break;

            case ARC_OPERAND_BRAKET:
              if (tok[tokidx].X_op != O_bracket) {
                current_opcode_match_failed = true;
              }
              break;

            case ARC_OPERAND_COLON:
              if (tok[tokidx].X_op != O_colon) {
                current_opcode_match_failed = true;
              }
              break;

            case ARC_OPERAND_LIMM:
            case ARC_OPERAND_SIGNED:
            case ARC_OPERAND_UNSIGNED:
              if (!handle_numeric_operand_logic(opcode, operand, tok, tokidx, &current_ntok, prev_tok, &operand_specific_errmsg)) {
                  current_opcode_match_failed = true;
              }
              break;

            default:
              gas_assert(0 && "Unexpected operand typecheck mask for a non-fake operand");
              current_errmsg = _("internal error: unexpected operand type");
              current_opcode_match_failed = true;
              break;
            }

          if (current_opcode_match_failed) {
            current_errmsg = operand_specific_errmsg ? operand_specific_errmsg : _("operand mismatch");
            break;
          }
          prev_tok = &tok[tokidx];
	      ++tokidx;
	    }

      if (current_opcode_match_failed) {
        if (tokidx >= max_error_idx && current_errmsg) {
            max_error_idx = tokidx;
            best_errmsg = current_errmsg;
        }
        continue;
      }

      if (!parse_opcode_flags(opcode, nflgs, first_pflag)) {
        current_errmsg = _("flag mismatch");
        if (tokidx >= max_error_idx && current_errmsg) {
            max_error_idx = tokidx;
            best_errmsg = current_errmsg;
        }
        continue;
      }

      if (tokidx != current_ntok) {
        current_errmsg = (tokidx < current_ntok) ? _("missing operand") : _("too many arguments");
        if (tokidx >= max_error_idx && current_errmsg) {
            max_error_idx = tokidx;
            best_errmsg = current_errmsg;
        }
        continue;
      }

      *pntok = current_ntok;
      if (pcpumatch) {
        *pcpumatch = got_cpu_match;
      }
      return opcode;
    }

  if (pcpumatch) {
    *pcpumatch = got_cpu_match;
  }
  if (errmsg && best_errmsg) {
    *errmsg = best_errmsg;
  }
  return NULL;
}

static bool
check_operand_addrtype_logic(const struct arc_operand *operand,
                             const expressionS *token,
                             const char **errmsg_out)
{
  if (token->X_op != O_addrtype) {
    return false;
  }
  gas_assert(operand->insert != NULL);
  const char *tmpmsg_local = NULL;
  (*operand->insert)(0, token->X_add_number, &tmpmsg_local);
  if (tmpmsg_local != NULL) {
    *errmsg_out = tmpmsg_local;
    return false;
  }
  return true;
}

static bool
check_operand_ir_logic(const struct arc_operand *operand,
                       expressionS *token_base_ptr,
                       int token_idx,
                       int *p_current_ntok,
                       const expressionS *prev_token,
                       const char **errmsg_out)
{
  expressionS *current_token = &token_base_ptr[token_idx];

  if ((current_token->X_op != O_register || !is_ir_num(current_token->X_add_number))
      && !(operand->flags & ARC_OPERAND_IGNORE)) {
    return false;
  }

  if (operand->flags & ARC_OPERAND_DUPLICATE) {
    if (prev_token == NULL || prev_token->X_op != O_register
        || !is_ir_num(prev_token->X_add_number)
        || (regno(prev_token->X_add_number) != regno(current_token->X_add_number))) {
      return false;
    }
  }

  if (operand->insert) {
    const char *tmpmsg_local = NULL;
    (*operand->insert)(0, regno(current_token->X_add_number), &tmpmsg_local);
    if (tmpmsg_local) {
      if (operand->flags & ARC_OPERAND_IGNORE) {
        if (!allocate_tok(token_base_ptr, *p_current_ntok - 1, token_idx)) {
          *errmsg_out = _("internal error: failed to allocate token for ignored operand");
          return false;
        }
        current_token->X_op = O_absent;
        ++(*p_current_ntok);
      } else {
        *errmsg_out = tmpmsg_local;
        return false;
      }
    }
  }
  return true;
}

static bool
check_immediate_range_and_alignment_logic(const struct arc_operand *operand,
                                          offsetT value,
                                          const char **errmsg_out)
{
  if (operand->bits != 32 && !(operand->flags & ARC_OPERAND_NCHK)) {
    offsetT min_val, max_val;

    if (operand->flags & ARC_OPERAND_SIGNED) {
      max_val = (1LL << (operand->bits - 1)) - 1;
      min_val = -(1LL << (operand->bits - 1));
    } else {
      max_val = (1LL << operand->bits) - 1;
      min_val = 0;
    }

    if (value < min_val || value > max_val) {
      *errmsg_out = _("immediate is out of bounds");
      return false;
    }

    if ((operand->flags & ARC_OPERAND_ALIGNED32) && (value & 0x03)) {
      *errmsg_out = _("immediate is not 32bit aligned");
      return false;
    }
    if ((operand->flags & ARC_OPERAND_ALIGNED16) && (value & 0x01)) {
      *errmsg_out = _("immediate is not 16bit aligned");
      return false;
    }
  } else if (operand->flags & ARC_OPERAND_NCHK) {
    if (operand->insert) {
      const char *insert_msg = NULL;
      (*operand->insert)(0, value, &insert_msg);
      if (insert_msg) {
        *errmsg_out = insert_msg;
        return false;
      }
    } else if (!(operand->flags & ARC_OPERAND_IGNORE)) {
      return false;
    }
  }
  return true;
}

static bool
handle_numeric_operand_logic(const struct arc_opcode *opcode,
                             const struct arc_operand *operand,
                             expressionS *token_base_ptr,
                             int token_idx,
                             int *p_current_ntok,
                             const expressionS *prev_token,
                             const char **errmsg_out)
{
  expressionS *current_token = &token_base_ptr[token_idx];
  bool internal_success = false;

  switch (current_token->X_op) {
    case O_illegal:
    case O_absent:
    case O_register:
      break;

    case O_bracket:
      if (operand->flags & ARC_OPERAND_IGNORE) {
        if (!allocate_tok(token_base_ptr, *p_current_ntok - 1, token_idx)) {
          *errmsg_out = _("internal error: failed to allocate token for bracket");
          break;
        }
        current_token->X_op = O_absent;
        ++(*p_current_ntok);
        internal_success = true;
      }
      break;

    case O_symbol:
      if (opcode->insn_class != AUXREG) {
        break;
      }
      {
        const char *p = S_GET_NAME(current_token->X_add_symbol);
        char *tmpp = strdup(p);
        if (!tmpp) {
          *errmsg_out = _("memory allocation failed");
          break;
        }
        for (char *pp = tmpp; *pp; ++pp) *pp = TOLOWER(*pp);
        const struct arc_aux_reg *auxr = str_hash_find(arc_aux_hash, tmpp);
        free(tmpp);

        if (auxr) {
          current_token->X_op = O_constant;
          current_token->X_add_number = auxr->address;
          ARC_SET_FLAG(current_token->X_add_symbol, ARC_FLAG_AUX);
        } else {
          break;
        }
      }
    case O_constant:
      if (!check_immediate_range_and_alignment_logic(operand, current_token->X_add_number, errmsg_out)) {
        break;
      }
      internal_success = true;
      break;

    case O_subtract:
      if ((current_token->X_add_number == 0)
          && contains_register(current_token->X_add_symbol)
          && contains_register(current_token->X_op_symbol)) {
        int regs = get_register(current_token->X_add_symbol);
        regs <<= 16;
        regs |= get_register(current_token->X_op_symbol);
        if (operand->insert) {
          const char *insert_msg = NULL;
          (*operand->insert)(0, regs, &insert_msg);
          if (insert_msg) {
            *errmsg_out = insert_msg;
            break;
          }
          internal_success = true;
        }
      }
      break;

    default:
      if (operand->default_reloc == 0) {
        break;
      }

      switch (current_token->X_md) {
        case O_gotoff:
        case O_gotpc:
        case O_pcl:
        case O_tpoff:
        case O_dtpoff:
        case O_tlsgd:
        case O_tlsie:
          if (!(operand->flags & ARC_OPERAND_LIMM)) {
            break;
          }
        case O_absent:
          if (!generic_reloc_p(operand->default_reloc)) {
            break;
          }
          internal_success = true;
          break;
        default:
          break;
      }
      break;
  }

  if (!internal_success) {
    if (!*errmsg_out) {
      *errmsg_out = _("operand type mismatch or invalid value");
    }
    return false;
  }

  if (operand->flags & ARC_OPERAND_DUPLICATE) {
    if (prev_token == NULL
        || prev_token->X_op == O_illegal
        || prev_token->X_op == O_absent
        || prev_token->X_op == O_register
        || (prev_token->X_add_number != current_token->X_add_number)) {
      *errmsg_out = _("operand is not duplicate of the previous one");
      return false;
    }
  }

  return true;
}

/* Swap operand tokens.  */

static void
swap_operand (expressionS *operand_array,
	      unsigned source,
	      unsigned destination)
{
  if (operand_array == NULL)
    {
      return;
    }

  if (source == destination)
    {
      return;
    }

  expressionS temp_operand = operand_array[destination];
  operand_array[destination] = operand_array[source];
  operand_array[source] = temp_operand;
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
        {
          return true;
        }
      else if (!(operand_real->flags & ARC_OPERAND_IR))
        {
          offsetT val = tok->X_add_number + op->count;
          offsetT min_val, max_val;

          if (operand_real->flags & ARC_OPERAND_SIGNED)
            {
              offsetT two_to_power_n_minus_1 = ((offsetT)1 << (operand_real->bits - 1));
              min_val = -two_to_power_n_minus_1;
              max_val = two_to_power_n_minus_1 - 1;
            }
          else
            {
              max_val = (((offsetT)1 << operand_real->bits) - 1);
              min_val = 0;
            }
          return (val >= min_val && val <= max_val);
        }
      break;

    case O_symbol:
      return (operand_real->flags & ARC_OPERAND_LIMM)
             || ((operand_real->flags & ARC_OPERAND_SIGNED) && operand_real->bits == 9);

    case O_register:
      return (operand_real->flags & ARC_OPERAND_IR);

    case O_bracket:
      return (operand_real->flags & ARC_OPERAND_BRAKET);

    default:
      break;
    }

  return false;
}

/* Find pseudo instruction in array.  */

static const struct arc_pseudo_insn *
find_pseudo_insn (const char *opname,
		  int ntok,
		  const expressionS *tok)
{
  if (opname == NULL || ntok < 0)
    return NULL;
  if (ntok > 0 && tok == NULL)
    return NULL;

  unsigned int i;
  for (i = 0; i < arc_num_pseudo_insn; ++i)
    {
      const struct arc_pseudo_insn *current_insn = &arc_pseudo_insns[i];

      if (strcmp(current_insn->mnemonic_p, opname) == 0)
	{
	  if (current_insn->num_operands != ntok)
	    {
	      continue;
	    }

	  if (ntok > 0 && current_insn->operand == NULL)
	    {
	      continue;
	    }

	  const struct arc_operand_operation *op = current_insn->operand;
	  int j;
	  int operands_match = 1;

	  for (j = 0; j < ntok; ++j)
	    {
	      if (!pseudo_operand_match(&tok[j], &op[j]))
		{
		  operands_match = 0;
		  break;
		}
	    }

	  if (operands_match)
	    return current_insn;
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
  const struct arc_pseudo_insn *pseudo_insn;
  unsigned int i;
  int initial_ntok_count = *ntok;

  pseudo_insn = find_pseudo_insn (opname, initial_ntok_count, tok);

  if (pseudo_insn == NULL)
    return NULL;

  if (pseudo_insn->flag_r != NULL)
    {
      int flags_added = tokenize_flags (pseudo_insn->flag_r,
                                        &pflags[*nflgs],
                                        MAX_INSN_FLGS - *nflgs);
      if (flags_added < 0)
        return NULL;
      
      *nflgs += flags_added;
      if (*nflgs > MAX_INSN_FLGS) {
          *nflgs = MAX_INSN_FLGS;
      }
    }

  for (i = 0; i < pseudo_insn->operand_cnt; ++i)
    {
      const struct arc_operand_operation *operand_pseudo = &pseudo_insn->operand[i];

      if (operand_pseudo->operand_idx >= ARC_NUM_OPERANDS)
        {
          return NULL;
        }
      const struct arc_operand *operand_real = &arc_operands[operand_pseudo->operand_idx];

      if ((operand_real->flags & ARC_OPERAND_BRAKET) && !operand_pseudo->needs_insert)
        continue;

      if (i >= MAX_TOKENS)
        {
          return NULL;
        }

      if (operand_pseudo->needs_insert)
        {
          if (*ntok >= MAX_TOKENS) {
              return NULL;
          }

          if (operand_real->flags & ARC_OPERAND_BRAKET)
            {
              tok[i].X_op = O_bracket;
              ++(*ntok);
            }
          else
            {
              char construct_operand[MAX_CONSTR_STR];
              int snprintf_res;

              if (operand_real->flags & ARC_OPERAND_IR)
                snprintf_res = snprintf (construct_operand, MAX_CONSTR_STR, "r%d",
                                         operand_pseudo->count);
              else
                snprintf_res = snprintf (construct_operand, MAX_CONSTR_STR, "%d",
                                         operand_pseudo->count);

              if (snprintf_res < 0 || (unsigned int)snprintf_res >= MAX_CONSTR_STR)
                {
                  return NULL;
                }

              tokenize_arguments (construct_operand, &tok[i], 1);
              ++(*ntok);
            }
        }
      else if (operand_pseudo->count != 0)
        {
          if (i >= (unsigned int)initial_ntok_count) {
              return NULL;
          }

          switch (tok[i].X_op)
            {
            case O_constant:
              tok[i].X_add_number += operand_pseudo->count;
              break;

            case O_symbol:
              break;

            default:
              break;
            }
        }
    }

  for (i = 0; i < pseudo_insn->operand_cnt; ++i)
    {
      const struct arc_operand_operation *operand_pseudo = &pseudo_insn->operand[i];

      if (operand_pseudo->swap_operand_idx == i)
        continue;

      if (i >= pseudo_insn->operand_cnt || operand_pseudo->swap_operand_idx >= pseudo_insn->operand_cnt)
        {
          return NULL;
        }

      swap_operand (tok, i, operand_pseudo->swap_operand_idx);

      break;
    }

  return arc_find_opcode (pseudo_insn->mnemonic_r);
}

static const struct arc_opcode_hash_entry *
find_special_case_flag (const char *opname,
			int *nflgs,
			struct arc_flags *pflags)
{
  for (size_t i = 0; i < arc_num_flag_special; ++i)
    {
      const struct arc_flag_special *current_special_opcode = &arc_flag_special_cases[i];
      const char *special_opcode_name = current_special_opcode->name;
      size_t special_opcode_name_len = strlen (special_opcode_name);

      if (strncmp (opname, special_opcode_name, special_opcode_name_len) != 0)
	    continue;

      const char *opname_suffix = opname + special_opcode_name_len;

      for (size_t flag_arr_idx = 0; ; ++flag_arr_idx)
	    {
	      unsigned flag_idx = current_special_opcode->flags[flag_arr_idx];
	      if (flag_idx == 0)
	        break;

	      const char *flag_name_suffix = arc_flag_operands[flag_idx].name;
	      size_t flag_name_suffix_len = strlen (flag_name_suffix);

	      if (strcmp (opname_suffix, flag_name_suffix) == 0)
	        {
                const struct arc_opcode_hash_entry *entry_found = arc_find_opcode (special_opcode_name);

	            if (*nflgs >= MAX_INSN_FLGS)
	                break;

                size_t dest_buffer_capacity = sizeof(pflags[0].name);
	            if (flag_name_suffix_len >= dest_buffer_capacity)
	                break;

	            memcpy (pflags[*nflgs].name, flag_name_suffix, flag_name_suffix_len);
	            pflags[*nflgs].name[flag_name_suffix_len] = '\0';

	            (*nflgs)++;
	            return entry_found;
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

  entry = find_special_case_pseudo (opname, ntok, tok, nflgs, pflags);

  if (entry == NULL)
    {
      entry = find_special_case_flag (opname, nflgs, pflags);
    }

  return entry;
}

/* Autodetect cpu attribute list.  */

static void
autodetect_attributes (const struct arc_opcode *opcode,
			 const expressionS *tok,
			 int ntok)
{
  unsigned i;
  const struct mpy_type
  {
    unsigned feature;
    unsigned encoding;
  } mpy_list[] = {{ MPY1E, 1 }, { MPY6E, 6 }, { MPY7E, 7 }, { MPY8E, 8 },
		 { MPY9E, 9 }};

  for (i = 0; i < ARRAY_SIZE (feature_list); i++)
    if (opcode->subclass == feature_list[i].feature)
      selected_cpu.features |= feature_list[i].feature;

  for (i = 0; i < ARRAY_SIZE (mpy_list); i++)
    if (opcode->subclass == mpy_list[i].feature)
      mpy_option = mpy_list[i].encoding;

  const unsigned int rf16_exclude_reg_range1_min = 4;
  const unsigned int rf16_exclude_reg_range1_max = 9;
  const unsigned int rf16_exclude_reg_range2_min = 16;
  const unsigned int rf16_exclude_reg_range2_max = 25;

  for (i = 0; i < (unsigned) ntok; i++)
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
	}

      switch (tok[i].X_op)
	{
	case O_register:
	  if ((tok[i].X_add_number >= rf16_exclude_reg_range1_min && tok[i].X_add_number <= rf16_exclude_reg_range1_max)
	      || (tok[i].X_add_number >= rf16_exclude_reg_range2_min && tok[i].X_add_number <= rf16_exclude_reg_range2_max))
	    rf16_only = false;
	  break;
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
  const struct arc_opcode_hash_entry *entry = NULL;
  const struct arc_opcode *opcode = NULL;
  int cpumatch = 1;
  const char *errmsg = NULL;

  entry = arc_find_opcode (opname);

  if (entry == NULL)
    entry = find_special_case (opname, &nflgs, pflags, tok, &ntok);

  if (entry != NULL)
    {
      pr_debug ("%s:%d: assemble_tokens: %s\n",
		frag_now->fr_file, frag_now->fr_line, opname);

      opcode = find_opcode_match (entry, tok, &ntok, pflags,
				  nflgs, &cpumatch, &errmsg);
      if (opcode != NULL)
	{
	  struct arc_insn insn;

	  autodetect_attributes (opcode,  tok, ntok);
	  assemble_insn (opcode, tok, ntok, pflags, nflgs, &insn);
	  emit_insn (&insn);
	  return;
	}
    }

  if (entry == NULL)
    {
      as_bad (_("unknown opcode '%s'"), opname);
    }
  else
    {
      if (!cpumatch)
	{
	  as_bad (_("opcode '%s' not supported for target %s"), opname,
		  selected_cpu.name);
	}
      else
	{
	  if (errmsg)
	    as_bad (_("%s for instruction '%s'"), errmsg, opname);
	  else
	    as_bad (_("inappropriate arguments for opcode '%s'"), opname);
	}
    }
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

  if ((nflg = tokenize_flags (str + opnamelen, flags, MAX_INSN_FLGS)) == -1)
    {
      as_bad (_("syntax error"));
      goto cleanup;
    }

  str += opnamelen;
  for (; !is_end_of_stmt (*str); str++)
    if (is_whitespace (*str))
      break;

  if ((ntok = tokenize_arguments (str, tok, MAX_INSN_ARGS)) < 0)
    {
      as_bad (_("syntax error"));
      goto cleanup;
    }

  assemble_tokens (opname, tok, ntok, flags, nflg);

cleanup:
  assembling_insn = false;
}

/* Callback to insert a register into the hash table.  */

static void
declare_register (const char *name, int number)
{
  symbolS *new_symbol = symbol_create (name, reg_section,
                                       &zero_address_frag, number);

  if (str_hash_insert (arc_reg_hash, S_GET_NAME (new_symbol), new_symbol, 0) != NULL)
    {
      symbol_free (new_symbol);
      as_fatal (_("duplicate %s"), name);
    }
}

/* Construct symbols for each of the general registers.  */

#include <stdio.h>

#define REGISTER_COUNT 64
#define MAX_NAME_LENGTH 32

static void
declare_register_set (void)
{
  int i;
  char name[MAX_NAME_LENGTH];

  for (i = 0; i < REGISTER_COUNT; ++i)
    {
      snprintf(name, MAX_NAME_LENGTH, "r%d", i);
      declare_register (name, i);

      if (i % 2 == 0)
	{
          snprintf(name, MAX_NAME_LENGTH, "r%dr%d", i, i + 1);
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
      as_fatal (_("Failed to create symbol for %s"), name);
    }

  if (str_hash_insert (arc_addrtype_hash, S_GET_NAME (addrtypeS), addrtypeS, 0) != 0)
    {
      as_fatal (_("duplicate %s"), name);
    }
}

/* Port-specific assembler initialization.  This function is called
   once, at assembler startup time.  */

#define ARC_OPCODE_HTAB_INITIAL_SIZE 16

void
md_begin (void)
{
  if (mach_selection_mode == MACH_SELECTION_NONE)
    arc_select_cpu(TARGET_WITH_CPU, MACH_SELECTION_FROM_DEFAULT);

  target_big_endian = (byte_order == BIG_ENDIAN);

  if (!bfd_set_arch_mach(stdoutput, bfd_arch_arc, selected_cpu.mach))
    as_warn(_("could not set architecture and machine"));

  bfd_set_private_flags(stdoutput, selected_cpu.eflags);

  arc_opcode_hash = htab_create_alloc(ARC_OPCODE_HTAB_INITIAL_SIZE,
                                      hash_string_tuple,
                                      eq_string_tuple,
                                      arc_opcode_free,
                                      xcalloc,
                                      free);
  if (arc_opcode_hash == NULL) {
    as_fatal(_("failed to create opcode hash table"));
  }

  const struct arc_opcode *current_opcode = arc_opcodes;
  while (current_opcode != NULL && current_opcode->name != NULL) {
    arc_insert_opcode(current_opcode);

    const char *current_name = current_opcode->name;
    do {
      current_opcode++;
    } while (current_opcode != NULL && current_opcode->name != NULL &&
             (current_opcode->name == current_name || !strcmp(current_opcode->name, current_name)));
  }

  arc_reg_hash = str_htab_create();
  if (arc_reg_hash == NULL) {
    as_fatal(_("failed to create register hash table"));
  }

  declare_register_set();
  declare_register("gp", 26);
  declare_register("fp", 27);
  declare_register("sp", 28);
  declare_register("ilink", 29);
  declare_register("ilink1", 29);
  declare_register("ilink2", 30);
  declare_register("blink", 31);

  declare_register("x0_u0", 32);
  declare_register("x0_u1", 33);
  declare_register("x1_u0", 34);
  declare_register("x1_u1", 35);
  declare_register("x2_u0", 36);
  declare_register("x2_u1", 37);
  declare_register("x3_u0", 38);
  declare_register("x3_u1", 39);
  declare_register("y0_u0", 40);
  declare_register("y0_u1", 41);
  declare_register("y1_u0", 42);
  declare_register("y1_u1", 43);
  declare_register("y2_u0", 44);
  declare_register("y2_u1", 45);
  declare_register("y3_u0", 46);
  declare_register("y3_u1", 47);
  declare_register("x0_nu", 48);
  declare_register("x1_nu", 49);
  declare_register("x2_nu", 50);
  declare_register("x3_nu", 51);
  declare_register("y0_nu", 52);
  declare_register("y1_nu", 53);
  declare_register("y2_nu", 54);
  declare_register("y3_nu", 55);

  declare_register("mlo", 57);
  declare_register("mmid", 58);
  declare_register("mhi", 59);

  declare_register("acc1", 56);
  declare_register("acc2", 57);

  declare_register("lp_count", 60);
  declare_register("pcl", 63);

  memset(arc_last_insns, 0, sizeof(arc_last_insns));

  arc_aux_hash = str_htab_create();
  if (arc_aux_hash == NULL) {
    as_fatal(_("failed to create auxiliary register hash table"));
  }

  for (unsigned int i = 0; i < arc_num_aux_regs; ++i) {
    const struct arc_aux_reg *current_auxr = &arc_aux_regs[i];

    if (!(current_auxr->cpu & selected_cpu.flags)) {
      continue;
    }

    if (current_auxr->subclass != NONE && !check_cpu_feature(current_auxr->subclass)) {
      continue;
    }

    if (str_hash_insert(arc_aux_hash, current_auxr->name, current_auxr, 0) != 0) {
      as_fatal(_("duplicate auxiliary register name '%s'"), current_auxr->name);
    }
  }

  arc_addrtype_hash = str_htab_create();
  if (arc_addrtype_hash == NULL) {
    as_fatal(_("failed to create address type hash table"));
  }

  declare_addrtype("bd", ARC_NPS400_ADDRTYPE_BD);
  declare_addrtype("jid", ARC_NPS400_ADDRTYPE_JID);
  declare_addrtype("lbd", ARC_NPS400_ADDRTYPE_LBD);
  declare_addrtype("mbd", ARC_NPS400_ADDRTYPE_MBD);
  declare_addrtype("sd", ARC_NPS400_ADDRTYPE_SD);
  declare_addrtype("sm", ARC_NPS400_ADDRTYPE_SM);
  declare_addrtype("xa", ARC_NPS400_ADDRTYPE_XA);
  declare_addrtype("xd", ARC_NPS400_ADDRTYPE_XD);
  declare_addrtype("cd", ARC_NPS400_ADDRTYPE_CD);
  declare_addrtype("cbd", ARC_NPS400_ADDRTYPE_CBD);
  declare_addrtype("cjid", ARC_NPS400_ADDRTYPE_CJID);
  declare_addrtype("clbd", ARC_NPS400_ADDRTYPE_CLBD);
  declare_addrtype("cm", ARC_NPS400_ADDRTYPE_CM);
  declare_addrtype("csd", ARC_NPS400_ADDRTYPE_CSD);
  declare_addrtype("cxa", ARC_NPS400_ADDRTYPE_CXA);
  declare_addrtype("cxd", ARC_NPS400_ADDRTYPE_CXD);
}

static void
delete_and_null_htab (htab_t *table_handle_ptr)
{
  if (table_handle_ptr != NULL && *table_handle_ptr != NULL)
    {
      htab_delete (*table_handle_ptr);
      *table_handle_ptr = NULL;
    }
}

void
arc_md_end (void)
{
  delete_and_null_htab (&arc_opcode_hash);
  delete_and_null_htab (&arc_reg_hash);
  delete_and_null_htab (&arc_aux_hash);
  delete_and_null_htab (&arc_addrtype_hash);
}

/* Write a value out to the object file, using the appropriate
   endianness.  */

#include <stddef.h>
#include <stdbool.h>

typedef unsigned long long valueT;

extern bool target_big_endian;
extern void number_to_chars_bigendian(char *buf, valueT val, int n);
extern void number_to_chars_littleendian(char *buf, valueT val, int n);

void
md_number_to_chars (char *buf,
		    valueT val,
		    int n)
{
  if (buf == NULL)
    {
      return;
    }

  if (target_big_endian)
    number_to_chars_bigendian (buf, val, n);
  else
    number_to_chars_littleendian (buf, val, n);
}

/* Round up a section size to the appropriate boundary.  */

valueT
md_section_align (segT segment,
		  valueT size)
{
  int align = bfd_section_alignment (segment);

  // Clamp 'align' to a valid range to prevent undefined behavior from shift operations.
  // The maximum valid exponent for a left shift is (number of bits in the type) - 1.
  // We assume CHAR_BIT is 8, which is common and often implicitly relied upon
  // when <limits.h> is not explicitly included for CHAR_BIT.
  const int max_align_exponent = sizeof(valueT) * 8 - 1;

  if (align < 0) {
      // A negative alignment exponent is nonsensical and leads to undefined behavior.
      // Treat it as no alignment (2^0 = 1) for a well-defined outcome.
      align = 0;
  }
  if (align > max_align_exponent) {
      // An alignment exponent exceeding the type's bit width leads to undefined behavior.
      // Clamp it to the maximum safe shift exponent to ensure a well-defined result.
      align = max_align_exponent;
  }

  // Calculate the actual alignment boundary (power of 2).
  // Explicitly cast `1` to `valueT` to ensure the shift operation is performed on the correct type
  // and to prevent potential overflow if `align` is large and `int` is smaller than `valueT`.
  const valueT alignment_value = (valueT)1 << align;

  // Perform the "round up to the nearest multiple of alignment_value" calculation.
  // This is a standard and efficient bitwise trick for power-of-2 alignment.
  // The pattern (X + A - 1) & (-A) is used as it matches the original logic.
  return (size + alignment_value - 1) & (-alignment_value);
}

/* The location from which a PC relative jump should be calculated,
   given a PC relative reloc.  */

long
md_pcrel_from_section (fixS *fixP,
		       segT sec)
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

  int adjustments_mask = 0; /* Bit 0: apply base -= 4; Bit 1: apply base &= ~3 */
  const int ADJUST_SUB_4 = 1;
  const int ADJUST_ALIGN_4 = 2;

  if ((int) fixP->fx_r_type < 0)
    {
      adjustments_mask |= ADJUST_ALIGN_4;
    }
  else
    {
      switch (fixP->fx_r_type)
	{
	case BFD_RELOC_ARC_PC32:
	  adjustments_mask |= ADJUST_SUB_4;
	  /* Fall through. */
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
	  adjustments_mask |= ADJUST_ALIGN_4;
	  break;
	default:
	  as_bad_where (fixP->fx_file, fixP->fx_line,
			_("unhandled reloc %s in md_pcrel_from_section"),
		  bfd_get_reloc_code_name (fixP->fx_r_type));
	  break;
	}
    }

  if (adjustments_mask & ADJUST_SUB_4)
    {
      base -= 4;
    }
  if (adjustments_mask & ADJUST_ALIGN_4)
    {
      base &= ~3;
    }

  pr_debug ("pcrel from %" PRIx64 " + %lx = %" PRIx64 ", "
	    "symbol: %s (%" PRIx64 ")\n",
	    (uint64_t) fixP->fx_frag->fr_address, fixP->fx_where, (uint64_t) base,
	    fixP->fx_addsy ? S_GET_NAME (fixP->fx_addsy) : "(null)",
	    fixP->fx_addsy ? (uint64_t) S_GET_VALUE (fixP->fx_addsy) : (uint64_t) 0);

  return (long) base;
}

/* Given a BFD relocation find the corresponding operand.  */

static const struct arc_operand *
find_operand_for_reloc (extended_bfd_reloc_code_real_type reloc)
{
  size_t i;

  for (i = 0; i < arc_num_operands; i++)
    if (arc_operands[i].default_reloc == reloc)
      return &arc_operands[i];
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
  long long range_min = 0;
  long long range_max = 0;

  // Determine if a range check is needed based on operand properties.
  const bool perform_range_check = !(operand->bits == 32
                                     || (operand->flags & ARC_OPERAND_NCHK)
                                     || (operand->flags & ARC_OPERAND_FAKE));

  if (perform_range_check)
    {
      if (operand->flags & ARC_OPERAND_SIGNED)
	{
	  if (operand->bits == 0)
	    {
	      range_min = 0;
	      range_max = 0;
	      // A 0-bit signed field can only hold 0.
	      if (val != 0)
		{
		  as_bad_value_out_of_range (_("operand"), val, range_min, range_max, file, line);
		}
	    }
	  else if (operand->bits >= 64) // For 64-bit signed, the range is [LLONG_MIN, LLONG_MAX]
	    {
	      range_min = LLONG_MIN;
	      range_max = LLONG_MAX;
	      // `val` is already `long long`, so it cannot exceed this range.
	      // No `as_bad_value_out_of_range` will be triggered by `val < range_min || val > range_max` here.
	    }
	  else // Bits between 1 and 63 for signed operand
	    {
	      // Calculate max_val = 2^(bits-1) - 1 and min_val = -2^(bits-1)
	      unsigned long long limit_val = 1ULL << (operand->bits - 1);
	      range_max = (long long) (limit_val - 1);
	      range_min = (long long) -limit_val;

	      if (val < range_min || val > range_max)
		{
		  as_bad_value_out_of_range (_("operand"), val, range_min, range_max, file, line);
		}
	    }
	}
      else /* Unsigned */
	{
	  range_min = 0; // Unsigned fields always have a minimum of 0.

	  if (operand->bits == 0)
	    {
	      range_max = 0;
	      // A 0-bit unsigned field can only hold 0.
	      if (val != 0)
		{
		  as_bad_value_out_of_range (_("operand"), val, range_min, range_max, file, line);
		}
	    }
	  else if (operand->bits >= 64) // For 64-bit unsigned, max is ULLONG_MAX
	    {
	      // `as_bad_value_out_of_range` takes `long long` for `max`.
	      // `ULLONG_MAX` cannot be fully represented in `long long`.
	      // We use `LLONG_MAX` as a practical display limit for the diagnostic message.
	      range_max = LLONG_MAX;

	      // Actual range check for `val` against `ULLONG_MAX`.
	      // `val` can be negative, which is always out of range for unsigned.
	      unsigned long long target_unsigned_max = ~0ULL; // Represents ULLONG_MAX
	      if (val < 0 || (unsigned long long)val > target_unsigned_max)
		{
		  as_bad_value_out_of_range (_("operand"), val, range_min, range_max, file, line);
		}
	    }
	  else // Bits between 1 and 63 for unsigned operand
	    {
	      // Calculate max_val = 2^bits - 1
	      unsigned long long max_unsigned_val = (1ULL << operand->bits) - 1;
	      range_max = (long long) max_unsigned_val;

	      // Check `val` against the calculated unsigned range.
	      // `val` can be negative, which is always out of range for unsigned.
	      if (val < 0 || (unsigned long long)val > max_unsigned_val)
		{
		  as_bad_value_out_of_range (_("operand"), val, range_min, range_max, file, line);
		}
	    }
	}
    }

  pr_debug ("insert field: %ld <= %lld <= %ld in 0x%08llx\n",
            range_min, val, range_max, insn);

  // Constants for alignment masks
  const int ALIGNED32_MASK = 0x03; // Mask for 4-byte alignment (bits 0 and 1)
  const int ALIGNED16_MASK = 0x01; // Mask for 2-byte alignment (bit 0)

  if ((operand->flags & ARC_OPERAND_ALIGNED32) && (val & ALIGNED32_MASK))
    {
      as_bad_where (file, line, _("Unaligned operand. Needs to be 32bit aligned"));
    }

  if ((operand->flags & ARC_OPERAND_ALIGNED16) && (val & ALIGNED16_MASK))
    {
      as_bad_where (file, line, _("Unaligned operand. Needs to be 16bit aligned"));
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
      if (operand->flags & ARC_OPERAND_TRUNCATE)
	{
	  // Note: Both alignment shifts can apply if both flags are set,
	  // reflecting the original code's behavior.
	  if (operand->flags & ARC_OPERAND_ALIGNED32)
	    {
	      val >>= 2;
	    }
	  if (operand->flags & ARC_OPERAND_ALIGNED16)
	    {
	      val >>= 1;
	    }
	}

      // Determine the mask for the operand's bit width, handling edge cases for 0 or 64 bits.
      unsigned long long mask;
      if (operand->bits == 64)
	{
	  mask = ~0ULL; // All bits set for 64-bit mask
	}
      else if (operand->bits == 0)
	{
	  mask = 0ULL; // No bits set for 0-bit mask
	}
      else
	{
	  mask = (1ULL << operand->bits) - 1;
	}

      // Apply the mask and shift the value into the instruction.
      // Cast `val` to `unsigned long long` before bitwise operations to match `insn` type
      // and ensure consistent behavior for negative `val` when masking.
      insn |= (((unsigned long long)val & mask) << operand->shift);
    }
  return insn;
}

/* Apply a fixup to the object code.  At this point all symbol values
   should be fully resolved, and we attempt to completely resolve the
   reloc.  If we can not do that, we determine the correct reloc code
   and put it back in the fixup.  To indicate that a fixup has been
   eliminated, set fixP->fx_done.  */

static bool
handle_symbol_subtraction_and_check_error (fixS *fixP, symbolS **fx_subsyP, offsetT *fx_offsetP, segT *sub_symbol_segmentP)
{
  if (!*fx_subsyP)
    return true;

  bool is_tls_reloc = (fixP->fx_r_type == BFD_RELOC_ARC_TLS_DTPOFF ||
                       fixP->fx_r_type == BFD_RELOC_ARC_TLS_DTPOFF_S9 ||
                       fixP->fx_r_type == BFD_RELOC_ARC_TLS_GD_LD);

  if (is_tls_reloc)
    return true;

  resolve_symbol_value (*fx_subsyP);
  *sub_symbol_segmentP = S_GET_SEGMENT (*fx_subsyP);

  if (*sub_symbol_segmentP == absolute_section)
    {
      *fx_offsetP -= S_GET_VALUE (*fx_subsyP);
      *fx_subsyP = NULL;
    }
  else
    {
      as_bad_subtract (fixP);
      return false;
    }
  return true;
}

static void
handle_symbol_addition_and_pcrel_reset (fixS *fixP, valueT *valueP, offsetT *fx_offsetP, segT seg, symbolS **fx_addsyP, segT add_symbol_segment)
{
  if (!*fx_addsyP || S_IS_WEAK (*fx_addsyP))
    return;

  if (add_symbol_segment == seg && fixP->fx_pcrel)
    {
      *valueP += S_GET_VALUE (*fx_addsyP);
      *valueP -= md_pcrel_from_section (fixP, seg);
      *fx_addsyP = NULL;
      fixP->fx_pcrel = false;
    }
  else if (add_symbol_segment == absolute_section)
    {
      *valueP = fixP->fx_offset;
      *fx_offsetP += S_GET_VALUE (*fx_addsyP);
      *fx_addsyP = NULL;
      fixP->fx_pcrel = false;
    }

  if (!*fx_addsyP)
    fixP->fx_done = true;
}

static void
handle_pcrel_adjustments (fixS *fixP, valueT *valueP, segT seg)
{
  if (!fixP->fx_pcrel)
    return;

  if (fixP->fx_addsy
      && ((S_IS_DEFINED (fixP->fx_addsy) && S_GET_SEGMENT (fixP->fx_addsy) != seg)
          || S_IS_WEAK (fixP->fx_addsy)))
    *valueP += md_pcrel_from_section (fixP, seg);

  switch (fixP->fx_r_type)
    {
    case BFD_RELOC_ARC_32_ME:
      fixP->fx_offset += fixP->fx_frag->fr_address;
    case BFD_RELOC_32:
      fixP->fx_r_type = BFD_RELOC_ARC_PC32;
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
handle_tls_relocations (fixS *fixP, offsetT *fx_offsetP)
{
  extended_bfd_reloc_code_real_type reloc = fixP->fx_r_type;

  switch (reloc)
    {
    case BFD_RELOC_ARC_TLS_DTPOFF:
    case BFD_RELOC_ARC_TLS_LE_32:
      if (fixP->fx_done)
        break;
    case BFD_RELOC_ARC_TLS_GD_GOT:
    case BFD_RELOC_ARC_TLS_IE_GOT:
      S_SET_THREAD_LOCAL (fixP->fx_addsy);
      break;

    case BFD_RELOC_ARC_TLS_GD_LD:
      gas_assert (!fixP->fx_offset);
      if (fixP->fx_subsy)
        {
          *fx_offsetP = (S_GET_VALUE (fixP->fx_subsy)
                         - fixP->fx_frag->fr_address - fixP->fx_where);
        }
      fixP->fx_subsy = NULL;
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
map_plt_reloc_to_base (extended_bfd_reloc_code_real_type reloc_type)
{
  switch (reloc_type)
    {
    case BFD_RELOC_ARC_S25H_PCREL_PLT: return BFD_RELOC_ARC_S25W_PCREL;
    case BFD_RELOC_ARC_S21H_PCREL_PLT: return BFD_RELOC_ARC_S21H_PCREL;
    case BFD_RELOC_ARC_S25W_PCREL_PLT: return BFD_RELOC_ARC_S25W_PCREL;
    case BFD_RELOC_ARC_S21W_PCREL_PLT: return BFD_RELOC_ARC_S21W_PCREL;
    default: return reloc_type;
    }
}

static void
apply_final_simple_relocations (fixS *fixP, char *fixpos, valueT value, bool *done)
{
  *done = false;
  extended_bfd_reloc_code_real_type reloc = fixP->fx_r_type;

  switch (reloc)
    {
    case BFD_RELOC_8:
    case BFD_RELOC_16:
    case BFD_RELOC_24:
    case BFD_RELOC_32:
    case BFD_RELOC_64:
    case BFD_RELOC_ARC_32_PCREL:
      md_number_to_chars (fixpos, value, fixP->fx_size);
      *done = true;
      return;

    case BFD_RELOC_ARC_GOTPC32:
      as_bad (_("Unsupported operation on reloc"));
      *done = true;
      return;

    case BFD_RELOC_ARC_TLS_DTPOFF:
    case BFD_RELOC_ARC_TLS_LE_32:
      gas_assert (!fixP->fx_addsy);
      gas_assert (!fixP->fx_subsy);
    case BFD_RELOC_ARC_GOTOFF:
    case BFD_RELOC_ARC_32_ME:
    case BFD_RELOC_ARC_PC32:
    case BFD_RELOC_ARC_PLT32:
      md_number_to_chars_midend (fixpos, value, fixP->fx_size);
      *done = true;
      return;

    default:
      return;
    }
}

static void
apply_final_complex_relocations (fixS *fixP, extended_bfd_reloc_code_real_type *relocP, const struct arc_operand **operandP)
{
  extended_bfd_reloc_code_real_type current_reloc = *relocP;

  switch (current_reloc)
    {
    case BFD_RELOC_ARC_S25H_PCREL_PLT:
    case BFD_RELOC_ARC_S21H_PCREL_PLT:
    case BFD_RELOC_ARC_S25W_PCREL_PLT:
    case BFD_RELOC_ARC_S21W_PCREL_PLT:
    case BFD_RELOC_ARC_S25W_PCREL:
    case BFD_RELOC_ARC_S21W_PCREL:
    case BFD_RELOC_ARC_S21H_PCREL:
    case BFD_RELOC_ARC_S25H_PCREL:
    case BFD_RELOC_ARC_S13_PCREL:
      *operandP = find_operand_for_reloc (map_plt_reloc_to_base (current_reloc));
      gas_assert (*operandP);
      break;

    default:
      {
        if ((int) fixP->fx_r_type >= 0)
          as_fatal (_("unhandled relocation type %s"),
                    bfd_get_reloc_code_name (fixP->fx_r_type));

        if (fixP->fx_addsy != 0
            && S_GET_SEGMENT (fixP->fx_addsy) != absolute_section)
          as_bad_where (fixP->fx_file, fixP->fx_line,
                        _("non-absolute expression in constant field"));

        gas_assert (-(int) fixP->fx_r_type < (int) arc_num_operands);
        *operandP = &arc_operands[-(int) fixP->fx_r_type];
        break;
      }
    }
}

static unsigned int
read_instruction_value (const fixS *fixP, const char *fixpos)
{
  unsigned int insn = 0;

  if (target_big_endian)
    {
      switch (fixP->fx_size)
        {
        case 4: insn = bfd_getb32 (fixpos); break;
        case 2: insn = bfd_getb16 (fixpos); break;
        default:
          as_bad_where (fixP->fx_file, fixP->fx_line, _("unknown fixup size"));
          return 0;
        }
    }
  else
    {
      switch (fixP->fx_size)
        {
        case 4: insn = bfd_getl16 (fixpos) << 16 | bfd_getl16 (fixpos + 2); break;
        case 2: insn = bfd_getl16 (fixpos); break;
        default:
          as_bad_where (fixP->fx_file, fixP->fx_line, _("unknown fixup size"));
          return 0;
        }
    }
  return insn;
}

void
md_apply_fix (fixS *fixP,
	      valueT *valP,
	      segT seg)
{
  char * const fixpos = fixP->fx_frag->fr_literal + fixP->fx_where;
  valueT value = *valP;
  unsigned int insn = 0;
  symbolS *fx_addsy = fixP->fx_addsy;
  symbolS *fx_subsy = fixP->fx_subsy;
  offsetT fx_offset = 0;
  segT add_symbol_segment = absolute_section;
  segT sub_symbol_segment = absolute_section;
  const struct arc_operand *operand = NULL;

  pr_debug ("%s:%u: apply_fix: r_type=%d (%s) value=0x%lX offset=0x%lX\n",
	    fixP->fx_file, fixP->fx_line, fixP->fx_r_type,
	    ((int) fixP->fx_r_type < 0) ? "Internal":
	    bfd_get_reloc_code_name (fixP->fx_r_type), value,
	    fixP->fx_offset);

  if (fx_addsy)
    add_symbol_segment = S_GET_SEGMENT (fx_addsy);

  if (!handle_symbol_subtraction_and_check_error (fixP, &fx_subsy, &fx_offset, &sub_symbol_segment))
    return;

  handle_symbol_addition_and_pcrel_reset (fixP, &value, &fx_offset, seg, &fx_addsy, add_symbol_segment);

  handle_pcrel_adjustments (fixP, &value, seg);

  pr_debug ("%s:%u: apply_fix: r_type=%d (%s) value=0x%lX offset=0x%lX\n",
	    fixP->fx_file, fixP->fx_line, fixP->fx_r_type,
	    ((int) fixP->fx_r_type < 0) ? "Internal":
	    bfd_get_reloc_code_name (fixP->fx_r_type), value,
	    fixP->fx_offset);

  handle_tls_relocations (fixP, &fx_offset);

  if (!fixP->fx_done)
    {
      return;
    }

  value += fx_offset;

  if (value & 0x80000000UL)
    value |= (~0UL << 31);

  bool final_write_completed = false;
  apply_final_simple_relocations (fixP, fixpos, value, &final_write_completed);
  if (final_write_completed)
    return;

  extended_bfd_reloc_code_real_type current_reloc_type = fixP->fx_r_type;
  apply_final_complex_relocations (fixP, &current_reloc_type, &operand);

  gas_assert (operand);

  insn = read_instruction_value (fixP, fixpos);

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
  int growth;

  void *current_symbol = fragP->fr_symbol;
  segT symbol_segment = S_GET_SEGMENT(current_symbol);
  
  bool is_symbol_in_different_non_absolute_section = 
      (symbol_segment != segment && symbol_segment != absolute_section);
  
  bool is_constant_and_instruction_not_pcrel = 
      (symbol_constant_p(current_symbol) && !fragP->tc_frag_data.pcrel);
  
  bool is_symbol_equated_to_another = symbol_equated_p(current_symbol);
  
  bool is_symbol_weak = S_IS_WEAK(current_symbol);

  if (is_symbol_in_different_non_absolute_section ||
      is_constant_and_instruction_not_pcrel ||
      is_symbol_equated_to_another ||
      is_symbol_weak)
    {
      while (md_relax_table[fragP->fr_subtype].rlx_more != ARC_RLX_NONE)
	++fragP->fr_subtype;
    }

  growth = md_relax_table[fragP->fr_subtype].rlx_length;
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

  reloc = notes_alloc (sizeof (arelent));
  reloc->sym_ptr_ptr = notes_alloc (sizeof (asymbol *));
  *reloc->sym_ptr_ptr = symbol_get_bfdsym (fixP->fx_addsy);
  reloc->address = fixP->fx_frag->fr_address + fixP->fx_where;

  gas_assert ((int) fixP->fx_r_type > 0);

  code = fixP->fx_r_type;

  if (code == BFD_RELOC_ARC_GOTPC32
      && GOT_symbol
      && fixP->fx_addsy == GOT_symbol)
    code = BFD_RELOC_ARC_GOTPC;

  reloc->howto = bfd_reloc_type_lookup (stdoutput, code);
  if (reloc->howto == NULL)
    {
      as_bad_where (fixP->fx_file, fixP->fx_line,
		    _("cannot represent `%s' relocation in object file"),
		    bfd_get_reloc_code_name (code));
      return NULL;
    }

  if (!!fixP->fx_pcrel ^ !!reloc->howto->pc_relative)
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
  if (fragP->fr_subtype < 0 || fragP->fr_subtype >= arc_num_relax_opcodes) {
    as_fatal (_("no relaxation found for this instruction."));
  }

  const int fix = fragP->fr_fix;
  char *const dest = fragP->fr_literal + fix;
  const relax_typeS *const table_entry = TC_GENERIC_RELAX_TABLE + fragP->fr_subtype;
  const struct arc_opcode *const opcode = &arc_relax_opcodes[fragP->fr_subtype];
  struct arc_insn insn;
  struct arc_relax_type *const relax_arg = &fragP->tc_frag_data;

  pr_debug ("%s:%d: md_convert_frag, subtype: %d, fix: %d, "
	    "var: %" PRId64 "\n",
	    fragP->fr_file, fragP->fr_line,
	    fragP->fr_subtype, fix, (int64_t) fragP->fr_var);

  assemble_insn (opcode, relax_arg->tok, relax_arg->ntok, relax_arg->pflags,
	relax_arg->nflg, &insn);

  apply_fixups (&insn, fragP, fix);

  const int calculated_size = insn.len + (insn.has_limm ? 4 : 0);
  gas_assert (table_entry->rlx_length == calculated_size);

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
  if (name == NULL)
    {
      return NULL;
    }

  if (strcmp (name, GLOBAL_OFFSET_TABLE_NAME) == 0)
    {
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
  return NULL;
}

/* Turn a string in input_line_pointer into a floating point constant
   of type type, and store the appropriate bytes in *litP.  The number
   of LITTLENUMS emitted is stored in *sizeP.  An error message is
   returned, or NULL on OK.  */

const char *
md_atof (int type, char *litP, int *sizeP)
{
  int target_endianness_value = target_big_endian;
  return ieee_md_atof (type, litP, sizeP, target_endianness_value);
}

/* Called for any expression that can not be recognized.  When the
   function is called, `input_line_pointer' will point to the start of
   the expression.  We use it when we have complex operations like
   @label1 - @label2.  */

void
md_operand (expressionS *expressionP)
{
  if (expressionP == NULL)
    {
      return;
    }

  if (input_line_pointer == NULL)
    {
      return;
    }

  char *p = input_line_pointer;
  if (*p == '@')
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

static bool
assign_if_found (struct expressionS *e, struct hash_table *hash,
                 const char *name, enum expression_op op_type)
{
  struct symbol *sym = str_hash_find (hash, name);
  if (sym)
    {
      e->X_op = op_type;
      e->X_add_number = S_GET_VALUE (sym);
      return true;
    }
  return false;
}

bool
arc_parse_name (const char *name,
		struct expressionS *e)
{
  if (name == NULL || e == NULL)
    {
      return false;
    }

  if (!assembling_insn)
    {
      return false;
    }

  if (e->X_op == O_symbol
      && e->X_md == O_absent)
    {
      return false;
    }

  if (assign_if_found (e, arc_reg_hash, name, O_register))
    {
      return true;
    }

  if (assign_if_found (e, arc_addrtype_hash, name, O_addrtype))
    {
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

static int
apply_cpu_selection (const char *cpu_name)
{
  arc_select_cpu (cpu_name, MACH_SELECTION_FROM_COMMAND_LINE);
  return 1;
}

static void
apply_arc_feature (unsigned int feature)
{
  selected_cpu.features |= feature;
  cl_features |= feature;
  arc_check_feature ();
}

int
md_parse_option (int c, const char *arg ATTRIBUTE_UNUSED)
{
  switch (c)
    {
    case OPTION_ARC600:
    case OPTION_ARC601:
      return apply_cpu_selection ("arc600");

    case OPTION_ARC700:
      return apply_cpu_selection ("arc700");

    case OPTION_ARCEM:
      return apply_cpu_selection ("arcem");

    case OPTION_ARCHS:
      return apply_cpu_selection ("archs");

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
      apply_arc_feature (CD);
      break;

    case OPTION_RELAX:
      relaxation_state = 1;
      break;

    case OPTION_NPS400:
      apply_arc_feature (NPS400);
      break;

    case OPTION_SPFP:
      apply_arc_feature (SPX);
      break;

    case OPTION_DPFP:
      apply_arc_feature (DPX);
      break;

    case OPTION_FPUDA:
      apply_arc_feature (DPA);
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

#include <stdio.h>
#include <string.h>
#include <stdbool.h>

#define ARC_MAX_LINE_WIDTH    80
#define ARC_INDENT_LEN        26
static const char ARC_INDENT_STR[] = "                          ";

static void
arc_show_cpu_list (FILE *stream)
{
  if (stream == NULL)
    {
      return;
    }

  int current_line_offset = 0;

  fprintf(stream, "%s", ARC_INDENT_STR);
  current_line_offset = ARC_INDENT_LEN;

  for (int i = 0; cpu_types[i].name != NULL; ++i)
    {
      const char *cpu_name = cpu_types[i].name;
      size_t name_len = strlen(cpu_name);
      bool is_last_cpu = (cpu_types[i + 1].name == NULL);

      const char *separator_str_to_print = is_last_cpu ? "\n" : ", ";
      size_t separator_len_for_offset = is_last_cpu ? 0 : 2;

      if (current_line_offset + name_len + separator_len_for_offset > ARC_MAX_LINE_WIDTH)
        {
          fprintf(stream, "\n%s", ARC_INDENT_STR);
          current_line_offset = ARC_INDENT_LEN;
        }

      fprintf(stream, "%s%s", cpu_name, separator_str_to_print);
      current_line_offset += name_len + separator_len_for_offset;
    }
}


static void
print_md_general_intro (FILE *stream)
{
  fprintf (stream, _("ARC-specific assembler options:\n"));
}

static void
print_md_cpu_specific_options (FILE *stream)
{
  fprintf (stream, "  -mcpu=<cpu name>\t  (default: %s), assemble for"
           " CPU <cpu name>, one of:\n", TARGET_WITH_CPU);
  arc_show_cpu_list (stream);
  fprintf (stream, "\n");
  fprintf (stream, "  -mA6/-mARC600/-mARC601  same as -mcpu=arc600\n");
  fprintf (stream, "  -mA7/-mARC700\t\t  same as -mcpu=arc700\n");
  fprintf (stream, "  -mEM\t\t\t  same as -mcpu=arcem\n");
  fprintf (stream, "  -mHS\t\t\t  same as -mcpu=archs\n");
}

static void
print_md_instruction_extensions (FILE *stream)
{
  fprintf (stream, "  -mnps400\t\t  enable NPS-400 extended instructions\n");
  fprintf (stream, "  -mspfp\t\t  enable single-precision floating point"
	   " instructions\n");
  fprintf (stream, "  -mdpfp\t\t  enable double-precision floating point"
	   " instructions\n");
  fprintf (stream, "  -mfpuda\t\t  enable double-precision assist floating "
                   "point\n\t\t\t  instructions for ARC EM\n");
  fprintf (stream,
	   "  -mcode-density\t  enable code density option for ARC EM\n");
}

static void
print_md_endian_and_relax_options (FILE *stream)
{
  fprintf (stream, _("\
  -EB                     assemble code for a big-endian cpu\n"));
  fprintf (stream, _("\
  -EL                     assemble code for a little-endian cpu\n"));
  fprintf (stream, _("\
  -mrelax                 enable relaxation\n"));
}

static void
print_md_deprecated_options_list (FILE *stream)
{
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

void
md_show_usage (FILE *stream)
{
  print_md_general_intro(stream);
  print_md_cpu_specific_options(stream);
  print_md_instruction_extensions(stream);
  print_md_endian_and_relax_options(stream);
  print_md_deprecated_options_list(stream);
}

/* Find the proper relocation for the given opcode.  */

#include <stdbool.h>
#include <string.h>

// Assuming the following are defined globally or in other included headers:
// - extended_bfd_reloc_code_real_type
// - BFD_RELOC_UNUSED
// - struct arc_flags
// - struct arc_reloc_equiv_tab
// - arc_num_equiv_tab
// - arc_reloc_equiv[]
// - arc_flag_operands[]
// - as_bad()
// - _() (for internationalization)

// Helper function to check if all required flags are present in the provided input flags.
// `required_flags` is an array of unsigned integers, terminated by 0.
// `input_flags` is an array of `struct arc_flags`.
// `num_input_flags` is the number of elements in `input_flags`.
static bool
flags_match_criteria (const unsigned *required_flags,
                      const struct arc_flags *input_flags,
                      int num_input_flags)
{
  // If `required_flags` is NULL or the first element is 0,
  // it means no flags are required, so it's always a match.
  if (!required_flags || required_flags[0] == 0)
    return true;

  // If required flags exist but no input flags are provided, it's a mismatch.
  if (num_input_flags <= 0)
    return false;

  const unsigned *current_required_flag_idx = required_flags;
  while (*current_required_flag_idx != 0)
    {
      bool found_in_input = false;
      // Assuming arc_flag_operands is a global array of struct arc_flags
      // and *current_required_flag_idx is a valid index into it.
      const char *required_flag_name = arc_flag_operands[*current_required_flag_idx].name;

      for (int i = 0; i < num_input_flags; ++i)
        {
          if (strcmp (input_flags[i].name, required_flag_name) == 0)
            {
              found_in_input = true;
              break;
            }
        }

      // If a required flag was not found in the input flags, then this entry doesn't match.
      if (!found_in_input)
        return false;

      ++current_required_flag_idx;
    }

  // All required flags were found in the input flags.
  return true;
}

static extended_bfd_reloc_code_real_type
find_reloc (const char *name,
	    const char *opcodename,
	    const struct arc_flags *pflags,
	    int nflg,
	    extended_bfd_reloc_code_real_type reloc)
{
  unsigned int i;
  extended_bfd_reloc_code_real_type ret = BFD_RELOC_UNUSED;

  for (i = 0; i < arc_num_equiv_tab; i++)
    {
      const struct arc_reloc_equiv_tab *r = &arc_reloc_equiv[i];

      // 1. Check if the relocation entry's name matches.
      if (strcmp (name, r->name) != 0)
	continue;

      // 2. Check if the relocation entry's mnemonic (if specified) matches the opcode name.
      if (r->mnemonic && (strcmp (r->mnemonic, opcodename) != 0))
	continue;

      // 3. Check if all required flags for this relocation entry are present
      // in the provided input flags.
      // The `flags_match_criteria` helper handles cases where `r->flags` specifies no
      // required flags, or when `nflg` (number of input flags) is zero.
      if (!flags_match_criteria (r->flags, pflags, nflg))
          continue;

      // 4. Check if the relocation entry's oldreloc matches the input reloc.
      if (reloc != r->oldreloc)
	continue;

      // All criteria matched, so this is the correct relocation entry.
      ret = r->newreloc;
      break;
    }

  // If no matching relocation was found after checking all entries, report an error.
  if (ret == BFD_RELOC_UNUSED)
    as_bad (_("Unable to find %s relocation for instruction %s"),
	    name, opcodename);
  return ret;
}

/* All the symbol types that are allowed to be used for
   relaxation.  */

static bool
may_relax_expr (expressionS tok)
{
  return tok.X_md != O_plt && (
           tok.X_op == O_symbol ||
           tok.X_op == O_multiply ||
           tok.X_op == O_divide ||
           tok.X_op == O_modulus ||
           tok.X_op == O_add ||
           tok.X_op == O_subtract
         );
}

/* Checks if flags are in line with relaxable insn.  */

static bool
relaxable_flag (const struct arc_relaxable_ins *ins,
		const struct arc_flags *pflags,
		int nflgs)
{
  // If no flags are required, the condition is vacuously true.
  // This handles the case where nflgs is 0, which would otherwise result
  // in 'counttrue' remaining 0 and the final check '0 == 0' returning true.
  if (nflgs == 0)
    {
      return true;
    }

  unsigned int flag_class_idx = 0;
  int counttrue = 0;

  // Iterate through flag classes specified in 'ins'.
  // The loop continues as long as a non-zero flag class ID is found,
  // indicating a sentinel-terminated array of flag class IDs.
  while (ins->flag_classes[flag_class_idx] != 0)
    {
      const unsigned int current_flag_class = ins->flag_classes[flag_class_idx];
      unsigned int flag_id_idx = 0;

      // Iterate through individual flags within the current flag class.
      // This loop also uses a non-zero ID as a sentinel for the flags array.
      // It's assumed that 'current_flag_class' is a valid index into 'arc_flag_classes'.
      while (arc_flag_classes[current_flag_class].flags[flag_id_idx] != 0)
	{
	  const unsigned int flag_id = arc_flag_classes[current_flag_class].flags[flag_id_idx];
	  
	  // Retrieve the flag operand details using the 'flag_id'.
	  // It's assumed that 'flag_id' is a valid index into 'arc_flag_operands'.
	  const struct arc_flag_operand *flag_opand = &arc_flag_operands[flag_id];

	  // Compare the current flag operand's name with each required flag name in 'pflags'.
	  // The original function's logic requires counting all possible matches,
	  // meaning a single 'flag_opand' can match multiple 'pflags[i]' entries,
	  // and a 'pflags[i]' entry can be matched by multiple 'flag_opand' entries.
	  for (int i = 0; i < nflgs; ++i)
	    {
	      if (strcmp(flag_opand->name, pflags[i].name) == 0)
		{
		  ++counttrue;
		}
	    }
	  ++flag_id_idx;
	}
      ++flag_class_idx;
    }

  // The condition for relaxability is met if the total count of matches
  // found across all available flags equals the total number of required flags.
  return counttrue == nflgs;
}

/* Checks if operands are in line with relaxable insn.  */

#define ARC_GP_REGISTER 26

static bool
is_valid_immediate_op_code (enum expression_opcode op)
{
  switch (op)
    {
    case O_multiply:
    case O_divide:
    case O_modulus:
    case O_add:
    case O_subtract:
    case O_symbol:
      return true;
    default:
      return false;
    }
}

static bool
is_valid_register_s_number (int reg_num)
{
  switch (reg_num)
    {
    case 0:
    case 1:
    case 2:
    case 3:
    case 12:
    case 13:
    case 14:
    case 15:
      return true;
    default:
      return false;
    }
}

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

      const enum rlx_operand_type current_operand_type = ins->operands[i];
      const expressionS *current_token_expr = &tok[i];

      switch (current_operand_type)
        {
        case IMMEDIATE:
          if (!is_valid_immediate_op_code(current_token_expr->X_op))
            {
              return false;
            }
          break;

        case REGISTER_DUP:
          if (i == 0 || current_token_expr->X_add_number != tok[i - 1].X_add_number)
            {
              return false;
            }
        case REGISTER:
          if (current_token_expr->X_op != O_register)
            {
              return false;
            }
          break;

        case REGISTER_S:
          if (current_token_expr->X_op != O_register)
            {
              return false;
            }
          if (!is_valid_register_s_number(current_token_expr->X_add_number))
            {
              return false;
            }
          break;

        case REGISTER_NO_GP:
          if (current_token_expr->X_op != O_register || current_token_expr->X_add_number == ARC_GP_REGISTER)
            {
              return false;
            }
          break;

        case BRACKET:
          if (current_token_expr->X_op != O_bracket)
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
  if (opcode == NULL || tok == NULL || pflags == NULL)
    {
      return false;
    }

  if (ntok < 0 || nflg < 0)
    {
      return false;
    }

  if (!relaxation_state)
    {
      return false;
    }

  if (frag_now == NULL)
    {
      return false;
    }

  unsigned i;
  for (i = 0; i < arc_num_relaxable_ins; ++i)
    {
      const struct arc_relaxable_ins *arc_rlx_ins = &arc_relaxable_insns[i];

      if (strcmp (opcode->name, arc_rlx_ins->mnemonic_r) == 0)
	{
	  if (arc_rlx_ins->opcheckidx < 0 || arc_rlx_ins->opcheckidx >= ntok)
	    {
	      continue;
	    }

	  if (may_relax_expr (tok[arc_rlx_ins->opcheckidx])
	      && relaxable_operand (arc_rlx_ins, tok, ntok)
	      && relaxable_flag (arc_rlx_ins, pflags, nflg))
	    {
	      frag_now->fr_subtype = arc_rlx_ins->subtype;
	      memcpy (&frag_now->tc_frag_data.tok, tok,
		      sizeof (expressionS) * ntok);
	      memcpy (&frag_now->tc_frag_data.pflags, pflags,
		      sizeof (struct arc_flags) * nflg);
	      frag_now->tc_frag_data.nflg = nflg;
	      frag_now->tc_frag_data.ntok = ntok;
	      return true;
	    }
	}
    }

  return false;
}

/* Turn an opcode description and a set of arguments into
   an instruction and a fixup.  */

static void add_insn_fixup(struct arc_insn *insn,
                           const expressionS *exp,
                           extended_bfd_reloc_code_real_type reloc_code,
                           unsigned char pcrel_flag,
                           bool is_long_operand);

static bool handle_register_range_operand(unsigned long long *image,
                                         const struct arc_operand *operand,
                                         const expressionS *t);

static void handle_operand_relocation(struct arc_insn *insn,
                                     const struct arc_opcode *opcode,
                                     const struct arc_operand *operand,
                                     const expressionS *t,
                                     const struct arc_flags *pflags,
                                     int nflg,
                                     const expressionS **reloc_exp_out,
                                     unsigned char *pcrel_out);

static bool handle_arcv2_conditional_flag(struct arc_insn *insn,
                                          const struct arc_opcode *opcode,
                                          const struct arc_flag_operand *flg_operand,
                                          const expressionS *reloc_exp,
                                          unsigned char pcrel,
                                          unsigned long long *image);


static void
add_insn_fixup(struct arc_insn *insn,
               const expressionS *exp,
               extended_bfd_reloc_code_real_type reloc_code,
               unsigned char pcrel_flag,
               bool is_long_operand)
{
  if (insn->nfixups >= MAX_INSN_FIXUPS)
    as_fatal(_("too many fixups"));

  struct arc_fixup *fixup = &insn->fixups[insn->nfixups++];
  fixup->exp = *exp;
  fixup->reloc = reloc_code;
  fixup->pcrel = pcrel_flag;
  fixup->islong = is_long_operand;
}

static bool
handle_register_range_operand(unsigned long long *image,
                             const struct arc_operand *operand,
                             const expressionS *t)
{
  if ((t->X_add_number == 0)
      && contains_register(t->X_add_symbol)
      && contains_register(t->X_op_symbol))
    {
      int regs;
      regs = get_register(t->X_add_symbol);
      regs <<= 16;
      regs |= get_register(t->X_op_symbol);
      *image = insert_operand(*image, operand, regs, NULL, 0);
      return true;
    }
  return false;
}

static void
handle_operand_relocation(struct arc_insn *insn,
                         const struct arc_opcode *opcode,
                         const struct arc_operand *operand,
                         const expressionS *t,
                         const struct arc_flags *pflags,
                         int nflg,
                         const expressionS **reloc_exp_out,
                         unsigned char *pcrel_out)
{
  bool needGOTSymbol = false;
  extended_bfd_reloc_code_real_type reloc = BFD_RELOC_UNUSED;

  switch (t->X_md)
    {
    case O_plt:
      if (opcode->insn_class == JUMP)
        as_bad(_("Unable to use @plt relocation for insn %s"), opcode->name);
      needGOTSymbol = true;
      reloc = find_reloc("plt", opcode->name, pflags, nflg, operand->default_reloc);
      break;

    case O_gotoff:
    case O_gotpc:
      needGOTSymbol = true;
      reloc = ARC_RELOC_TABLE(t->X_md)->reloc;
      break;

    case O_pcl:
      if (operand->flags & ARC_OPERAND_LIMM)
        {
          reloc = ARC_RELOC_TABLE(t->X_md)->reloc;
          if (arc_opcode_len(opcode) == 2 || opcode->insn_class == JUMP)
            as_bad(_("Unable to use @pcl relocation for insn %s"), opcode->name);
        }
      else
        {
          reloc = operand->default_reloc;
        }
      break;

    case O_sda:
      reloc = find_reloc("sda", opcode->name, pflags, nflg, operand->default_reloc);
      break;

    case O_tlsgd:
    case O_tlsie:
      needGOTSymbol = true;
    case O_tpoff:
    case O_dtpoff:
      reloc = ARC_RELOC_TABLE(t->X_md)->reloc;
      break;

    case O_tpoff9:
    case O_dtpoff9:
      as_bad(_("TLS_*_S9 relocs are not supported yet"));
      break;

    default:
      reloc = operand->default_reloc;
      break;
    }

  if (needGOTSymbol && (GOT_symbol == NULL))
    GOT_symbol = symbol_find_or_make(GLOBAL_OFFSET_TABLE_NAME);

  *reloc_exp_out = t;

  unsigned char pcrel_val = 0;
  if ((int)reloc < 0)
    pcrel_val = (operand->flags & ARC_OPERAND_PCREL) ? 1 : 0;
  else
    {
      reloc_howto_type *reloc_howto = bfd_reloc_type_lookup(stdoutput, reloc);
      pcrel_val = reloc_howto->pc_relative;
    }
  *pcrel_out = pcrel_val;

  add_insn_fixup(insn, t, reloc, pcrel_val, (operand->flags & ARC_OPERAND_LIMM) != 0);
}

static bool
handle_arcv2_conditional_flag(struct arc_insn *insn,
                              const struct arc_opcode *opcode,
                              const struct arc_flag_operand *flg_operand,
                              const expressionS *reloc_exp,
                              unsigned char pcrel,
                              unsigned long long *image)
{
  if ((selected_cpu.flags & ARC_OPCODE_ARCV2)
      && (!strcmp(flg_operand->name, "t") || !strcmp(flg_operand->name, "nt")))
    {
      if (reloc_exp == NULL)
        {
          as_bad(_("Conditional flag '%s' requires a relocatable operand for insn %s"),
                 flg_operand->name, opcode->name);
          return true;
        }

      unsigned bitYoperand = 0;
      if (!strcmp(flg_operand->name, "t"))
        if (!strcmp(opcode->name, "bbit0") || !strcmp(opcode->name, "bbit1"))
          bitYoperand = arc_NToperand;
        else
          bitYoperand = arc_Toperand;
      else
        if (!strcmp(opcode->name, "bbit0") || !strcmp(opcode->name, "bbit1"))
          bitYoperand = arc_Toperand;
        else
          bitYoperand = arc_NToperand;

      if (reloc_exp->X_op == O_constant)
        {
          offsetT val = reloc_exp->X_add_number;
          *image = insert_operand(*image, &arc_operands[bitYoperand], val, NULL, 0);
        }
      else
        {
          add_insn_fixup(insn, reloc_exp, (extended_bfd_reloc_code_real_type)-bitYoperand, pcrel, false);
        }
      return true;
    }
  return false;
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
  unsigned long long image;
  const unsigned char *argidx;
  int i;
  int tokidx = 0;
  unsigned char pcrel = 0;
  bool has_delay_slot = false;

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
          tokidx ++;
          continue;
        }

      if (tokidx >= ntok)
        {
          as_fatal (_("Missing operand for '%s' instruction"), opcode->name);
          return;
        }
      else
        t = &tok[tokidx++];

      if (operand->flags & ARC_OPERAND_LIMM)
        insn->has_limm = true;

      switch (t->X_op)
        {
        case O_register:
          image = insert_operand (image, operand, regno (t->X_add_number),
                                  NULL, 0);
          break;

        case O_constant:
          image = insert_operand (image, operand, t->X_add_number, NULL, 0);
          reloc_exp = t;
          if (operand->flags & ARC_OPERAND_LIMM)
            insn->limm = t->X_add_number;
          break;

        case O_bracket:
        case O_colon:
        case O_addrtype:
          break;

        case O_absent:
          gas_assert (operand->flags & ARC_OPERAND_IGNORE);
          break;

        case O_subtract:
          if (handle_register_range_operand(&image, operand, t))
            break;

        default:
          handle_operand_relocation(insn, opcode, operand, t, pflags, nflg, &reloc_exp, &pcrel);
          break;
        }
    }

  for (i = 0; i < nflg; i++)
    {
      const struct arc_flag_operand *flg_operand = pflags[i].flgp;

      if (!strcmp (flg_operand->name, "d"))
        {
          has_delay_slot = true;
          continue;
        }

      if (handle_arcv2_conditional_flag(insn, opcode, flg_operand, reloc_exp, pcrel, &image))
        {
          continue;
        }

      image |= (flg_operand->code & ((1 << flg_operand->bits) - 1))
        << flg_operand->shift;
    }

  insn->relax = relax_insn_p (opcode, tok, ntok, pflags, nflg);

  insn->len = arc_opcode_len (opcode);

  insn->insn = image;

  arc_last_insns[1]            = arc_last_insns[0];
  arc_last_insns[0].opcode     = opcode;
  arc_last_insns[0].has_limm   = insn->has_limm;
  arc_last_insns[0].has_delay_slot = has_delay_slot;

  if (arc_last_insns[1].has_delay_slot
      && is_br_jmp_insn_p (arc_last_insns[0].opcode))
    as_bad (_("Insn %s has a jump/branch instruction %s in its delay slot."),
            arc_last_insns[1].opcode->name,
            arc_last_insns[0].opcode->name);
  if (arc_last_insns[1].has_delay_slot
      && arc_last_insns[0].has_limm)
    as_bad (_("Insn %s has an instruction %s with limm in its delay slot."),
            arc_last_insns[1].opcode->name,
            arc_last_insns[0].opcode->name);
}

void
arc_handle_align (fragS* fragP)
{
  if (fragP == NULL || fragP->fr_next == NULL)
    {
      /* Input pointers are invalid, cannot proceed. */
      return;
    }

  if (fragP->fr_type == rs_align_code)
    {
      if (fragP->fr_literal == NULL)
        {
          /* fr_literal is NULL, cannot write data. */
          return;
        }

      char *dest_ptr = fragP->fr_literal + fragP->fr_fix;

      /* Calculate the number of bytes from the fragment's current address
       * to the start of the next fragment, after accounting for already
       * fixed content. This determines if padding is required for 2-byte alignment. */
      valueT bytes_to_align_for = fragP->fr_next->fr_address - fragP->fr_address - fragP->fr_fix;

      /* The 'fr_var' field is set to 2, representing the size of the NOP instruction
       * that will be written. This is the variable part of this fragment's output. */
      fragP->fr_var = 2;

      /* Check if the current position requires a 1-byte padding to achieve
       * 2-byte alignment for the subsequent NOP instruction. */
      if (bytes_to_align_for & 1)
        {
          /* Add one byte of zero padding. */
          *dest_ptr++ = 0;
          /* Increment 'fr_fix' to account for the added padding byte,
           * which effectively becomes part of the fixed-size output for this fragment. */
          fragP->fr_fix++;
        }

      /* Write the 2-byte NOP instruction at the current destination pointer.
       * 'dest_ptr' is correctly positioned after any potential padding. */
      md_number_to_chars (dest_ptr, NOP_OPCODE_S, 2);
    }
}

/* Here we decide which fixups can be adjusted to make them relative
   to the beginning of the section instead of the symbol.  Basically
   we need to make sure that the dynamic relocations are done
   correctly, so in some cases we force the original symbol to be
   used.  */

int
tc_arc_fix_adjustable (fixS *fixP)
{
  if (fixP == NULL)
    return 0;

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
      break;
    }

  return 1;
}

/* Compute the reloc type of an expression EXP.  */

static void
arc_check_reloc (expressionS *exp,
		 bfd_reloc_code_real_type *r_type_p)
{
  if (exp == NULL || r_type_p == NULL) {
    return;
  }

  if (*r_type_p == BFD_RELOC_32 &&
      exp->X_op == O_subtract &&
      exp->X_op_symbol != NULL &&
      S_GET_SEGMENT (exp->X_op_symbol) == now_seg) {
    *r_type_p = BFD_RELOC_ARC_32_PCREL;
  }
}


/* Add expression EXP of SIZE bytes to offset OFF of fragment FRAG.  */

void
arc_cons_fix_new (fragS *frag,
		  int off,
		  int size,
		  expressionS *exp)
{
  bfd_reloc_code_real_type r_type = BFD_RELOC_UNUSED;

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
      as_bad (_("unsupported BFD relocation size %u"), size);
      r_type = BFD_RELOC_UNUSED;
    }

  fix_new_exp (frag, off, size, exp, 0, r_type);
}

/* The actual routine that checks the ZOL conditions.  */

static void
check_zol (symbolS *s)
{
  const struct arc_insn_info *insn0 = &arc_last_insns[0];

  switch (selected_cpu.mach)
    {
    case bfd_mach_arc_arcv2:
      if (selected_cpu.flags & ARC_OPCODE_ARCv2EM)
        return;

      if (is_br_jmp_insn_p (insn0->opcode))
        {
          as_bad (_("Jump/Branch instruction detected at the end of the ZOL label @%s"),
                  S_GET_NAME (s));
        }
      else if (arc_insn_count >= 2)
        {
          const struct arc_insn_info *insn1 = &arc_last_insns[1];
          if (insn1->has_delay_slot)
            {
              as_bad (_("Jump/Branch instruction detected at the end of the ZOL label @%s"),
                      S_GET_NAME (s));
            }
        }
      break;

    case bfd_mach_arc_arc600:
      if (is_kernel_insn_p (insn0->opcode))
        as_bad (_("Kernel instruction detected at the end of the ZOL label @%s"),
                S_GET_NAME (s));

      if (insn0->has_limm && is_br_jmp_insn_p (insn0->opcode))
        as_bad (_("A jump instruction with long immediate detected at the end of the ZOL label @%s"), S_GET_NAME (s));

    case bfd_mach_arc_arc700:
      if (insn0->has_delay_slot)
        as_bad (_("An illegal use of delay slot detected at the end of the ZOL label @%s"),
                S_GET_NAME (s));

      break;
    default:
      break;
    }
}

/* If ZOL end check the last two instruction for illegals.  */
void
arc_frob_label (symbolS * sym)
{
  if (sym == NULL)
    {
      return;
    }

  if (ARC_GET_FLAG (sym) & ARC_FLAG_ZOL)
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
  if (fragP == NULL)
    {
      return 0;
    }

  long calculated_value = (long)fragP->fr_address + (long)fragP->fr_fix;

  pr_debug ("arc_pcrel_adjust: address=%ld, fix=%ld, PCrel %s\n",
	    (long)fragP->fr_address, (long)fragP->fr_fix,
	    fragP->tc_frag_data.pcrel ? "Y" : "N");

  if (!fragP->tc_frag_data.pcrel)
    {
      return (int)calculated_value;
    }

  return (int)(calculated_value & 0x03);
}

/* Initialize the DWARF-2 unwind information for this procedure.  */

#define ARC_SP_REGISTER_NUMBER 28

void
tc_arc_frame_initial_instructions (void)
{
  cfi_add_CFA_def_cfa (ARC_SP_REGISTER_NUMBER, 0);
}

int
tc_arc_regname_to_dw2regnum (char *regname)
{
  if (regname == NULL)
    {
      return -1;
    }

  struct symbol *sym;

  sym = str_hash_find (arc_reg_hash, regname);
  if (sym != NULL)
    {
      return S_GET_VALUE (sym);
    }

  return -1;
}

/* Adjust the symbol table.  Delete found AUX register symbols.  */

void
arc_adjust_symtab (void)
{
  symbolS *current_sym = symbol_rootP;
  symbolS *next_sym;

  while (current_sym != NULL)
    {
      next_sym = symbol_next (current_sym);
      if (ARC_GET_FLAG (current_sym) & ARC_FLAG_AUX)
        {
          symbol_remove (current_sym, &symbol_rootP, &symbol_lastP);
        }
      current_sym = next_sym;
    }

  elf_adjust_symtab ();
}

typedef struct {
  const char *name;
  unsigned int len;
  unsigned char attr_class;
} class_entry_t;

static int
expect_and_consume_comma(const char *error_msg)
{
  if (*input_line_pointer != ',')
    {
      as_bad(error_msg);
      ignore_rest_of_line();
      return 0;
    }
  input_line_pointer++;
  return 1;
}

static unsigned char
try_match_and_advance_class_token(const class_entry_t *table, unsigned int table_size)
{
  unsigned int i;
  for (i = 0; i < table_size; i++)
    {
      if (!strncmp(table[i].name, input_line_pointer, table[i].len))
        {
          unsigned char class_val = table[i].attr_class;
          input_line_pointer += table[i].len;
          return class_val;
        }
    }
  return 0;
}

static void
tokenize_extinsn (extInstruction_t *einsn)
{
  char *name_start_ptr;
  char char_after_name;
  char *insn_name;
  unsigned char major_opcode;
  unsigned char sub_opcode;
  unsigned char syntax_class = 0;
  unsigned char syntax_class_modifiers = 0;
  unsigned char suffix_class = 0;
  unsigned char matched_token_class;

  SKIP_WHITESPACE();

  name_start_ptr = input_line_pointer;
  char_after_name = get_symbol_name(&name_start_ptr);
  insn_name = xstrdup(input_line_pointer);
  restore_line_pointer(char_after_name);

  for (char *p = insn_name; *p; ++p)
    *p = TOLOWER(*p);

  if (!expect_and_consume_comma(_("expected comma after instruction name")))
    {
      return;
    }
  major_opcode = get_absolute_expression();

  SKIP_WHITESPACE();
  if (!expect_and_consume_comma(_("expected comma after major opcode")))
    {
      return;
    }
  sub_opcode = get_absolute_expression();

  SKIP_WHITESPACE();
  if (!expect_and_consume_comma("expected comma after sub opcode"))
    {
      return;
    }

  while (1)
    {
      SKIP_WHITESPACE();
      matched_token_class = try_match_and_advance_class_token(suffixclass, ARRAY_SIZE(suffixclass));
      if (matched_token_class == 0)
        {
          as_bad("invalid suffix class");
          ignore_rest_of_line();
          return;
        }
      suffix_class |= matched_token_class;

      SKIP_WHITESPACE();
      if (*input_line_pointer == '|')
        input_line_pointer++;
      else
        break;
    }

  if (!expect_and_consume_comma("expected comma after suffix class"))
    {
      return;
    }

  while (1)
    {
      SKIP_WHITESPACE();
      matched_token_class = try_match_and_advance_class_token(syntaxclassmod, ARRAY_SIZE(syntaxclassmod));
      if (matched_token_class != 0)
        {
          syntax_class_modifiers |= matched_token_class;
        }
      else
        {
          matched_token_class = try_match_and_advance_class_token(syntaxclass, ARRAY_SIZE(syntaxclass));
          if (matched_token_class != 0)
            {
              syntax_class |= matched_token_class;
            }
          else
            {
              as_bad("missing syntax class");
              ignore_rest_of_line();
              return;
            }
        }

      SKIP_WHITESPACE();
      if (*input_line_pointer == '|')
        input_line_pointer++;
      else
        break;
    }

  demand_empty_rest_of_line();

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
  if (!arcext_section)
    {
      arcext_section = subseg_new (".arcextmap", 0);
      if (!arcext_section)
        {
          return 0;
        }
      bfd_set_section_flags (arcext_section, SEC_READONLY | SEC_HAS_CONTENTS);
    }
  else
    {
      subseg_set (arcext_section, 0);
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

  size_t name_len = strlen (einsn->name);

  // Calculate the total size of the data block to be written.
  // This includes:
  //   1 byte for the total_packet_size field itself
  //   1 byte for EXT_INSTRUCTION type
  //   1 byte for major version
  //   1 byte for minor version
  //   1 byte for flags
  //   (name_len + 1) bytes for the null-terminated instruction name string
  // The first byte written (total_packet_size_byte) stores this total.
  size_t total_packet_size_val = 1 + 1 + 1 + 1 + 1 + (name_len + 1);

  // The first byte must be an unsigned char, implying the total packet size <= 255.
  // If name_len + 6 can exceed 255, this indicates a potential overflow in the original design.
  // We explicitly cast to ensure this matches the single-byte storage in the original logic.
  unsigned char total_packet_size_byte = (unsigned char) total_packet_size_val;

  arc_set_ext_seg ();

  // Allocate all required memory in a single call to frag_more.
  // This improves efficiency and maintainability.
  unsigned char *p = (unsigned char *) frag_more (total_packet_size_val);

  // Write the total size of the packet (including this byte).
  // This corresponds to the original *p = 5 + name_len + 1;
  *p++ = total_packet_size_byte;

  // Write the instruction type identifier.
  *p++ = EXT_INSTRUCTION;

  // Write major, minor versions, and flags.
  // Explicitly cast to unsigned char to ensure byte-level assignment and prevent
  // potential truncation or signed/unsigned issues if source fields are wider than a byte.
  *p++ = (unsigned char) einsn->major;
  *p++ = (unsigned char) einsn->minor;
  *p++ = (unsigned char) einsn->flags;

  // Copy the instruction name string, including the null terminator.
  // memcpy is used for safer and clearer byte array copying with an explicit length.
  memcpy (p, einsn->name, name_len + 1);

  // Restore the original segment context.
  subseg_set (old_sec, old_subsec);
}

/* Handler .extinstruction pseudo-op.  */

static void
arc_extinsn (int ignore ATTRIBUTE_UNUSED)
{
  extInstruction_t einsn;
  struct arc_opcode *arc_ext_opcodes;
  const char *errmsg = NULL;

  static const unsigned char ARC_MAJOR_OPCODE_LOW_BOUND = 0x05;
  static const unsigned char ARC_MAJOR_OPCODE_HIGH_BOUND_V2_EM_HS = 0x07;
  static const unsigned char ARC_MAJOR_OPCODE_HIGH_BOUND_OTHER = 0x0a;
  static const unsigned char ARC_MINOR_OPCODE_MAX = 0x3f;
  static const unsigned char ARC_MAJOR_OPCODE_MINOR_EXCEPTION_0A = 0x0a;
  static const unsigned char ARC_MAJOR_OPCODE_MINOR_EXCEPTION_05 = 0x05;
  static const unsigned char ARC_MAJOR_OPCODE_MINOR_EXCEPTION_09 = 0x09;

  unsigned char major_opcode_high_bound;

  memset (&einsn, 0, sizeof (einsn));
  tokenize_extinsn (&einsn);

  if (arc_find_opcode (einsn.name))
    as_warn (_("Pseudocode already used %s"), einsn.name);

  major_opcode_high_bound = (selected_cpu.flags & (ARC_OPCODE_ARCv2EM | ARC_OPCODE_ARCv2HS))
                          ? ARC_MAJOR_OPCODE_HIGH_BOUND_V2_EM_HS
                          : ARC_MAJOR_OPCODE_HIGH_BOUND_OTHER;

  if ((einsn.major > major_opcode_high_bound) || (einsn.major < ARC_MAJOR_OPCODE_LOW_BOUND))
    as_fatal (_("major opcode not in range [0x%02x - 0x%02x]"), ARC_MAJOR_OPCODE_LOW_BOUND, major_opcode_high_bound);

  if ((einsn.minor > ARC_MINOR_OPCODE_MAX) &&
      (einsn.major != ARC_MAJOR_OPCODE_MINOR_EXCEPTION_0A) &&
      (einsn.major != ARC_MAJOR_OPCODE_MINOR_EXCEPTION_05) &&
      (einsn.major != ARC_MAJOR_OPCODE_MINOR_EXCEPTION_09))
    as_fatal (_("minor opcode not in range [0x00 - 0x%02x]"), ARC_MINOR_OPCODE_MAX);

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
  if (arc_ext_opcodes == NULL)
    {
      if (errmsg)
	as_fatal ("%s", errmsg);
      else
	as_fatal (_("Couldn't generate extension instruction opcodes"));
    }
  else if (errmsg)
    as_warn ("%s", errmsg);

  arc_insert_opcode (arc_ext_opcodes);

  create_extinst_section (&einsn);
}

static bool
tokenize_extregister (extRegister_t *ereg, int opertype)
{
  char *name = NULL;
  char *mode_str;
  char c;
  char *p;
  int number, imode = 0;
  bool isCore_p = opertype == EXT_CORE_REGISTER;
  bool isReg_p = opertype == EXT_CORE_REGISTER || opertype == EXT_AUX_REGISTER;

#define CONSUME_COMMA(error_msg) \
  do { \
    SKIP_WHITESPACE (); \
    if (*input_line_pointer != ',') { \
      as_bad (error_msg); \
      ignore_rest_of_line (); \
      goto error_cleanup; \
    } \
    input_line_pointer++; \
  } while (0)

  SKIP_WHITESPACE ();
  p = input_line_pointer;
  c = get_symbol_name (&p);
  name = xstrdup (p);
  restore_line_pointer (c);

  CONSUME_COMMA (_("expected comma after name"));
  number = get_absolute_expression ();

  if (number < 0 && opertype != EXT_AUX_REGISTER)
    {
      as_bad (_("%s second argument cannot be a negative number %d"),
	      isCore_p ? "extCoreRegister's" : "extCondCode's",
	      number);
      ignore_rest_of_line ();
      goto error_cleanup;
    }

  if (isReg_p)
    {
      CONSUME_COMMA (_("expected comma after register number"));
      mode_str = input_line_pointer;

      if (startswith (mode_str, "r|w"))
	{
	  imode = 0;
	  input_line_pointer += 3;
	}
      else if (startswith (mode_str, "r"))
	{
	  imode = ARC_REGISTER_READONLY;
	  input_line_pointer += 1;
	}
      else if (startswith (mode_str, "w"))
	{
	  imode = ARC_REGISTER_WRITEONLY;
	  input_line_pointer += 1;
	}
      else
	{
	  as_bad (_("invalid mode"));
	  ignore_rest_of_line ();
	  goto error_cleanup;
	}
    }

  if (isCore_p)
    {
      CONSUME_COMMA (_("expected comma after register mode"));

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
	  ignore_rest_of_line ();
	  goto error_cleanup;
	}
    }
  demand_empty_rest_of_line ();

  ereg->name = name;
  ereg->number = number;
  ereg->imode  = imode;
  return true;

error_cleanup:
  free (name);
  return false;

#undef CONSUME_COMMA
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

static inline void write_byte_to_frag(unsigned char value) {
  char *p = frag_more(1);
  *p = value;
}

static inline void write_uint32_be_to_frag(uint32_t value) {
  char *p = frag_more(4);
  p[0] = (unsigned char)((value >> 24) & 0xff);
  p[1] = (unsigned char)((value >> 16) & 0xff);
  p[2] = (unsigned char)((value >>  8) & 0xff);
  p[3] = (unsigned char)(value        & 0xff);
}

#define FIXED_DATA_LEN_CORE_REG_NUMBER  1
#define FIXED_DATA_LEN_AUX_REG_NUMBER   4

static void
create_extcore_section (extRegister_t *ereg, int opertype)
{
  segT old_sec   = now_seg;
  int old_subsec = now_subseg;
  size_t name_len   = strlen (ereg->name);
  unsigned char payload_len_byte;

  arc_set_ext_seg ();

  switch (opertype)
    {
    case EXT_COND_CODE:
    case EXT_CORE_REGISTER:
      payload_len_byte = (unsigned char)(1 + FIXED_DATA_LEN_CORE_REG_NUMBER + name_len + 1);
      write_byte_to_frag(payload_len_byte);
      write_byte_to_frag((unsigned char)opertype);
      write_byte_to_frag((unsigned char)ereg->number);
      break;
    case EXT_AUX_REGISTER:
      payload_len_byte = (unsigned char)(1 + FIXED_DATA_LEN_AUX_REG_NUMBER + name_len + 1);
      write_byte_to_frag(payload_len_byte);
      write_byte_to_frag((unsigned char)EXT_AUX_REGISTER);
      write_uint32_be_to_frag(ereg->number);
      break;
    default:
      break;
    }

  char *p_name = frag_more (name_len + 1);
  strcpy (p_name, ereg->name);

  subseg_set (old_sec, old_subsec);
}

/* Handler .extCoreRegister pseudo-op.  */

#include <string.h>
#include <stdlib.h>

#define EXT_CORE_REGISTER 1
#define EXT_AUX_REGISTER 2
#define EXT_COND_CODE 3

#define ARC_CORE_REG_MAX_NUMBER 60
#define ARC_COND_CODE_MAX_NUMBER 31
#define ARC_FLAG_OPERAND_BITS 5
#define ARC_FLAG_OPERAND_SHIFT 0
#define ARC_FLAG_OPERAND_FAVAIL_UNUSED 0
#define ARC_AUX_REG_SUBCLASS_NONE 0

static void
arc_extcorereg (int opertype)
{
  extRegister_t ereg;
  struct arc_aux_reg *auxr;
  struct arc_flag_operand *ccode_new_slot;
  struct arc_flag_operand *new_arc_ext_condcode_ptr;

  memset (&ereg, 0, sizeof (ereg));
  if (!tokenize_extregister (&ereg, opertype))
    return;

  switch (opertype)
    {
    case EXT_CORE_REGISTER:
      if (ereg.number > ARC_CORE_REG_MAX_NUMBER)
	{
	  as_bad (_("core register %s value (%d) too large"), ereg.name,
		  ereg.number);
	}
      declare_register (ereg.name, ereg.number);
      break;

    case EXT_AUX_REGISTER:
      auxr = XNEW (struct arc_aux_reg);
      auxr->name = xstrdup (ereg.name);
      auxr->cpu = selected_cpu.flags;
      auxr->subclass = ARC_AUX_REG_SUBCLASS_NONE;
      auxr->address = ereg.number;

      if (str_hash_insert (arc_aux_hash, auxr->name, auxr, 0) != NULL)
	{
	  as_bad (_("duplicate aux register %s"), auxr->name);
	  free (auxr->name);
	  free (auxr);
	}
      break;

    case EXT_COND_CODE:
      if (ereg.number > ARC_COND_CODE_MAX_NUMBER)
	{
	  as_bad (_("condition code %s value (%d) too large"), ereg.name,
		  ereg.number);
	}

      ext_condcode.size++;
      new_arc_ext_condcode_ptr = XRESIZEVEC (struct arc_flag_operand,
                                             ext_condcode.arc_ext_condcode,
                                             ext_condcode.size + 1);
      ext_condcode.arc_ext_condcode = new_arc_ext_condcode_ptr;

      ccode_new_slot = ext_condcode.arc_ext_condcode + ext_condcode.size - 1;
      ccode_new_slot->name   = xstrdup (ereg.name);
      ccode_new_slot->code   = ereg.number;
      ccode_new_slot->bits   = ARC_FLAG_OPERAND_BITS;
      ccode_new_slot->shift  = ARC_FLAG_OPERAND_SHIFT;
      ccode_new_slot->favail = ARC_FLAG_OPERAND_FAVAIL_UNUSED;

      memset (ccode_new_slot + 1, 0, sizeof (struct arc_flag_operand));
      break;

    default:
      as_bad (_("Unknown extension"));
      break;
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
  if ((tag < 1
       || tag >= NUM_KNOWN_OBJ_ATTRIBUTES
       || !attributes_set_explicitly[tag])
      && !bfd_elf_add_proc_attr_int (stdoutput, tag, value))
    {
      as_fatal (_("error adding attribute: %s"),
		bfd_errmsg (bfd_get_error ()));
    }
}

static void
arc_set_attribute_string (int tag, const char *value)
{
  bool should_add_attribute = (tag < 1
                               || tag >= NUM_KNOWN_OBJ_ATTRIBUTES
                               || !attributes_set_explicitly[tag]);

  if (should_add_attribute)
    {
      if (!bfd_elf_add_proc_attr_string (stdoutput, tag, value))
        {
          as_fatal (_("error adding attribute: %s"),
                    bfd_errmsg (bfd_get_error ()));
        }
    }
}

/* Allocate and concatenate two strings.  s1 can be NULL but not
   s2.  s1 pointer is freed at end of this procedure.  */

static char *
arc_stralloc (char * s1, const char * s2)
{
  char * p;
  size_t s1_len = 0;
  size_t s2_len = 0;
  size_t total_len;

  gas_assert (s2);

  s2_len = strlen(s2);

  if (s1)
    {
      s1_len = strlen(s1);
      total_len = s1_len + 1 + s2_len + 1;
    }
  else
    {
      total_len = s2_len + 1;
    }

  p = xmalloc (total_len);

  if (s1)
    {
      snprintf(p, total_len, "%s,%s", s1, s2);
      free(s1);
    }
  else
    {
      snprintf(p, total_len, "%s", s2);
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

  switch (selected_cpu.eflags & EF_ARC_MACH_MSK)
    {
    case E_ARC_MACH_ARC600:
    case E_ARC_MACH_ARC601:
      base = TAG_CPU_ARC6xx;
      break;
    case E_ARC_MACH_ARC700:
      base = TAG_CPU_ARC7xx;
      break;
    case EF_ARC_CPU_ARCV2EM:
      base = TAG_CPU_ARCEM;
      break;
    case EF_ARC_CPU_ARCV2HS:
      base = TAG_CPU_ARCHS;
      break;
    default:
      base = 0;
      break;
    }

  if (attributes_set_explicitly[Tag_ARC_CPU_base])
    {
      int current_cpu_base_attr = bfd_elf_get_obj_attr_int (stdoutput, OBJ_ATTR_PROC, Tag_ARC_CPU_base);
      if (base != current_cpu_base_attr)
        {
          as_warn (_("Overwrite explicitly set Tag_ARC_CPU_base"));
        }
    }
  
  if (!bfd_elf_add_proc_attr_int (stdoutput, Tag_ARC_CPU_base, base))
    {
      as_fatal (_("error adding attribute: %s"),
	        bfd_errmsg (bfd_get_error ()));
    }

  if (attributes_set_explicitly[Tag_ARC_ABI_osver])
    {
      int val = bfd_elf_get_obj_attr_int (stdoutput, OBJ_ATTR_PROC, Tag_ARC_ABI_osver);
      selected_cpu.eflags = ((selected_cpu.eflags & ~EF_ARC_OSABI_MSK)
			     | (((unsigned int)val & 0x0fU) << 8));
    }
  else
    {
      arc_set_attribute_int (Tag_ARC_ABI_osver, E_ARC_OSABI_CURRENT >> 8);
    }

  arc_check_feature();

  for (i = 0; i < ARRAY_SIZE (feature_list); i++)
    {
      if (selected_cpu.features & feature_list[i].feature)
        {
          s = arc_stralloc (s, feature_list[i].attr);
        }
    }

  if (s)
    {
      arc_set_attribute_string (Tag_ARC_ISA_config, s);
    }

  arc_set_attribute_int (Tag_ARC_ISA_mpy_option, mpy_option);

  arc_set_attribute_int (Tag_ARC_ABI_pic, pic_option);

  arc_set_attribute_int (Tag_ARC_ABI_sda, sda_option);

  arc_set_attribute_int (Tag_ARC_ABI_tls, tls_option);

  arc_set_attribute_int (Tag_ARC_ATR_version, 1);

  if (attributes_set_explicitly[Tag_ARC_ABI_rf16])
    {
      int current_rf16_attr = bfd_elf_get_obj_attr_int (stdoutput, OBJ_ATTR_PROC, Tag_ARC_ABI_rf16);
      if (current_rf16_attr != 0 && !rf16_only)
        {
          as_warn (_("Overwrite explicitly set Tag_ARC_ABI_rf16 to full "
                     "register file"));
          if (!bfd_elf_add_proc_attr_int (stdoutput, Tag_ARC_ABI_rf16, 0))
            {
              as_fatal (_("error adding attribute: %s"),
                        bfd_errmsg (bfd_get_error ()));
            }
        }
    }
}

/* Add the default contents for the .ARC.attributes section.  */

void
arc_md_finish (void)
{
  arc_set_public_attributes ();

  if (!bfd_set_arch_mach (stdoutput, bfd_arch_arc, selected_cpu.mach))
    as_fatal (_("could not set architecture and machine"));

  if (!bfd_set_private_flags (stdoutput, selected_cpu.eflags))
    as_fatal (_("could not set private BFD flags"));
}

void arc_copy_symbol_attributes (symbolS *dest, symbolS *src)
{
  if (dest == ((void *)0) || src == ((void *)0))
  {
    return;
  }

  ARC_GET_FLAG (dest) = ARC_GET_FLAG (src);
}

int arc_convert_symbolic_attribute (const char *name)
{
  static const struct
  {
    const char * name;
    const int    tag;
  }
  attribute_table[] =
    {
#define T(tag) {#tag, tag}
  T (Tag_ARC_PCS_config),
  T (Tag_ARC_CPU_base),
  T (Tag_ARC_CPU_variation),
  T (Tag_ARC_CPU_name),
  T (Tag_ARC_ABI_rf16),
  T (Tag_ARC_ABI_osver),
  T (Tag_ARC_ABI_sda),
  T (Tag_ARC_ABI_pic),
  T (Tag_ARC_ABI_tls),
  T (Tag_ARC_ABI_enumsize),
  T (Tag_ARC_ABI_exceptions),
  T (Tag_ARC_ABI_double_size),
  T (Tag_ARC_ISA_config),
  T (Tag_ARC_ISA_apex),
  T (Tag_ARC_ISA_mpy_option),
  T (Tag_ARC_ATR_version)
#undef T
    };
  unsigned int i;

  if (name == NULL)
    return -1;

  for (i = 0; i < (sizeof(attribute_table) / sizeof(attribute_table[0])); i++)
    if (strcmp(name, attribute_table[i].name) == 0)
      return attribute_table[i].tag;

  return -1;
}

/* Local variables:
   eval: (c-set-style "gnu")
   indent-tabs-mode: t
   End:  */
