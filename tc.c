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
  return str_hash_find (arc_opcode_hash, name);
}

/* Initialise the iterator ITER.  */

static void
arc_opcode_hash_entry_iterator_init (struct arc_opcode_hash_entry_iterator *iter)
{
  iter->index = 0;
  iter->opcode = NULL;
}

/* Return the next ARC_OPCODE from ENTRY, using ITER to hold state between
   calls to this function.  Return NULL when all ARC_OPCODE entries have
   been returned.  */

static const struct arc_opcode *
initialize_iterator(const struct arc_opcode_hash_entry *entry,
                   struct arc_opcode_hash_entry_iterator *iter)
{
    gas_assert(entry->count > 0);
    iter->opcode = entry->opcode[iter->index];
    return iter->opcode;
}

static bool
is_same_opcode_name(const struct arc_opcode *opcode, const char *name)
{
    return opcode->name != NULL && strcmp(name, opcode->name) == 0;
}

static const struct arc_opcode *
advance_to_next_entry(const struct arc_opcode_hash_entry *entry,
                     struct arc_opcode_hash_entry_iterator *iter)
{
    iter->index++;
    if (iter->index == entry->count) {
        iter->opcode = NULL;
    } else {
        iter->opcode = entry->opcode[iter->index];
    }
    return iter->opcode;
}

static const struct arc_opcode *
advance_within_entry(const struct arc_opcode_hash_entry *entry,
                    struct arc_opcode_hash_entry_iterator *iter)
{
    const char *old_name = iter->opcode->name;
    iter->opcode++;
    
    if (!is_same_opcode_name(iter->opcode, old_name)) {
        return advance_to_next_entry(entry, iter);
    }
    
    return iter->opcode;
}

static const struct arc_opcode *
arc_opcode_hash_entry_iterator_next(const struct arc_opcode_hash_entry *entry,
                                   struct arc_opcode_hash_entry_iterator *iter)
{
    if (iter->opcode == NULL && iter->index == 0) {
        return initialize_iterator(entry, iter);
    }
    
    if (iter->opcode != NULL) {
        return advance_within_entry(entry, iter);
    }
    
    return iter->opcode;
}

/* Insert an opcode into opcode hash structure.  */

static struct arc_opcode_hash_entry *
find_or_create_hash_entry(const char *name)
{
    struct arc_opcode_hash_entry *entry = str_hash_find(arc_opcode_hash, name);
    
    if (entry == NULL)
    {
        entry = XNEW(struct arc_opcode_hash_entry);
        entry->count = 0;
        entry->opcode = NULL;
        
        if (str_hash_insert(arc_opcode_hash, name, entry, 0) != NULL)
            as_fatal(_("duplicate %s"), name);
    }
    
    return entry;
}

static void
add_opcode_to_entry(struct arc_opcode_hash_entry *entry, const struct arc_opcode *opcode)
{
    entry->opcode = XRESIZEVEC(const struct arc_opcode *, entry->opcode, entry->count + 1);
    entry->opcode[entry->count] = opcode;
    entry->count++;
}

static void
arc_insert_opcode(const struct arc_opcode *opcode)
{
    const char *name = opcode->name;
    struct arc_opcode_hash_entry *entry = find_or_create_hash_entry(name);
    add_opcode_to_entry(entry, opcode);
}

static void
arc_opcode_free (void *elt)
{
  string_tuple_t *tuple = elt;
  struct arc_opcode_hash_entry *entry = (void *) tuple->value;
  free (entry->opcode);
  free (entry);
  free (tuple);
}

/* Like md_number_to_chars but for middle-endian values.  The 4-byte limm
   value, is encoded as 'middle-endian' for a little-endian target.  This
   function is used for regular 4, 6, and 8 byte instructions as well.  */

static void md_number_to_chars_2_bytes(char *buf, unsigned long long val)
{
    md_number_to_chars(buf, val, 2);
}

static void md_number_to_chars_4_bytes(char *buf, unsigned long long val)
{
    const unsigned long long HIGH_WORD_MASK = 0xffff0000;
    const unsigned long long LOW_WORD_MASK = 0xffff;
    const int WORD_SHIFT = 16;
    const int WORD_SIZE = 2;
    
    md_number_to_chars(buf, (val & HIGH_WORD_MASK) >> WORD_SHIFT, WORD_SIZE);
    md_number_to_chars(buf + WORD_SIZE, (val & LOW_WORD_MASK), WORD_SIZE);
}

static void md_number_to_chars_6_bytes(char *buf, unsigned long long val)
{
    const unsigned long long HIGH_WORD_MASK = 0xffff00000000ull;
    const unsigned long long LOW_DWORD_MASK = 0xffffffff;
    const int HIGH_WORD_SHIFT = 32;
    const int WORD_SIZE = 2;
    const int DWORD_SIZE = 4;
    
    md_number_to_chars(buf, (val & HIGH_WORD_MASK) >> HIGH_WORD_SHIFT, WORD_SIZE);
    md_number_to_chars_midend(buf + WORD_SIZE, (val & LOW_DWORD_MASK), DWORD_SIZE);
}

static void md_number_to_chars_8_bytes(char *buf, unsigned long long val)
{
    const unsigned long long HIGH_DWORD_MASK = 0xffffffff00000000ull;
    const unsigned long long LOW_DWORD_MASK = 0xffffffff;
    const int DWORD_SHIFT = 32;
    const int DWORD_SIZE = 4;
    
    md_number_to_chars_midend(buf, (val & HIGH_DWORD_MASK) >> DWORD_SHIFT, DWORD_SIZE);
    md_number_to_chars_midend(buf + DWORD_SIZE, (val & LOW_DWORD_MASK), DWORD_SIZE);
}

static void md_number_to_chars_midend(char *buf, unsigned long long val, int n)
{
    switch (n)
    {
    case 2:
        md_number_to_chars_2_bytes(buf, val);
        break;
    case 4:
        md_number_to_chars_4_bytes(buf, val);
        break;
    case 6:
        md_number_to_chars_6_bytes(buf, val);
        break;
    case 8:
        md_number_to_chars_8_bytes(buf, val);
        break;
    default:
        abort();
    }
}

/* Check if a feature is allowed for a specific CPU.  */

static void arc_check_feature(void)
{
    if (!selected_cpu.features || !selected_cpu.name)
        return;

    check_feature_compatibility();
    check_feature_conflicts();
}

static void check_feature_compatibility(void)
{
    unsigned i;
    
    for (i = 0; i < ARRAY_SIZE(feature_list); i++)
    {
        if (is_feature_incompatible(i))
        {
            as_bad(_("invalid %s option for %s cpu"), 
                   feature_list[i].name,
                   selected_cpu.name);
        }
    }
}

static void check_feature_conflicts(void)
{
    unsigned i;
    
    for (i = 0; i < ARRAY_SIZE(conflict_list); i++)
    {
        if (has_conflicting_features(i))
        {
            as_bad(_("conflicting ISA extension attributes."));
        }
    }
}

static int is_feature_incompatible(unsigned index)
{
    return (selected_cpu.features & feature_list[index].feature) &&
           !(selected_cpu.flags & feature_list[index].cpus);
}

static int has_conflicting_features(unsigned index)
{
    return (selected_cpu.features & conflict_list[index]) == conflict_list[index];
}

/* Select an appropriate entry from CPU_TYPES based on ARG and initialise
   the relevant static global variables.  Parameter SEL describes where
   this selection originated from.  */

static void validate_selection_mode(enum mach_selection_type sel)
{
    if (sel == MACH_SELECTION_FROM_DEFAULT)
        gas_assert(mach_selection_mode == MACH_SELECTION_NONE);
    
    if (mach_selection_mode == MACH_SELECTION_FROM_CPU_DIRECTIVE &&
        sel == MACH_SELECTION_FROM_CPU_DIRECTIVE)
        as_bad(_("Multiple .cpu directives found"));
}

static int find_cpu_type_index(const char *arg)
{
    int i;
    for (i = 0; cpu_types[i].name; ++i)
    {
        if (!strcasecmp(cpu_types[i].name, arg))
            return i;
    }
    return -1;
}

static int handle_command_line_override(int cpu_index, enum mach_selection_type sel)
{
    if (mach_selection_mode != MACH_SELECTION_FROM_COMMAND_LINE)
        return 0;
    
    gas_assert(sel == MACH_SELECTION_FROM_COMMAND_LINE ||
               sel == MACH_SELECTION_FROM_CPU_DIRECTIVE);
    
    if (sel == MACH_SELECTION_FROM_CPU_DIRECTIVE &&
        selected_cpu.mach != cpu_types[cpu_index].mach)
    {
        as_warn(_("Command-line value overrides \".cpu\" directive"));
    }
    return 1;
}

static void update_selected_cpu(int cpu_index)
{
    selected_cpu.flags = cpu_types[cpu_index].flags;
    selected_cpu.name = cpu_types[cpu_index].name;
    selected_cpu.features = cpu_types[cpu_index].features | cl_features;
    selected_cpu.mach = cpu_types[cpu_index].mach;
    selected_cpu.eflags = ((selected_cpu.eflags & ~EF_ARC_MACH_MSK) |
                          cpu_types[cpu_index].eflags);
}

static void reinit_bfd_if_needed(struct cpu_type *old_cpu)
{
    if (mach_selection_mode == MACH_SELECTION_NONE)
        return;
    
    if (old_cpu->mach == selected_cpu.mach)
        return;
    
    bfd_find_target(arc_target_format, stdoutput);
    if (!bfd_set_arch_mach(stdoutput, bfd_arch_arc, selected_cpu.mach))
        as_warn(_("Could not set architecture and machine"));
}

static void arc_select_cpu(const char *arg, enum mach_selection_type sel)
{
    static struct cpu_type old_cpu = { 0, 0, 0, E_ARC_OSABI_CURRENT, 0 };
    int cpu_index;
    
    validate_selection_mode(sel);
    
    cpu_index = find_cpu_type_index(arg);
    if (cpu_index < 0)
        as_fatal(_("unknown architecture: %s\n"), arg);
    
    if (handle_command_line_override(cpu_index, sel))
        return;
    
    update_selected_cpu(cpu_index);
    arc_check_feature();
    reinit_bfd_if_needed(&old_cpu);
    
    mach_selection_mode = sel;
    old_cpu = selected_cpu;
}

/* Here ends all the ARCompact extension instruction assembling
   stuff.  */

static symbolS* parse_symbol_name(void)
{
    char *sym_name, c;
    symbolS *sym;
    
    c = get_symbol_name(&sym_name);
    sym = symbol_find_or_make(sym_name);
    restore_line_pointer(c);
    
    return sym;
}

static symbolS* parse_optional_label(int r_type)
{
    if (*input_line_pointer != ',' || r_type != BFD_RELOC_ARC_TLS_GD_LD)
        return NULL;
        
    ++input_line_pointer;
    return parse_symbol_name();
}

static void skip_at_symbol(void)
{
    if (*input_line_pointer == '@')
        input_line_pointer++;
}

static void create_relocation_fix(symbolS *sym, symbolS *lab, int r_type)
{
    #define RELOC_SIZE 0
    #define RELOC_ADDEND 0
    #define PC_RELATIVE false
    
    fixS *fixP = fix_new(frag_now,
                        frag_now_fix(),
                        RELOC_SIZE,
                        sym,
                        RELOC_ADDEND,
                        PC_RELATIVE,
                        r_type);
    fixP->fx_subsy = lab;
}

static void arc_extra_reloc(int r_type)
{
    symbolS *sym, *lab = NULL;
    
    skip_at_symbol();
    sym = parse_symbol_name();
    lab = parse_optional_label(r_type);
    create_relocation_fix(sym, lab, r_type);
}

static symbolS *
arc_lcomm_internal (int ignore ATTRIBUTE_UNUSED,
		    symbolS *symbolP, addressT size)
{
  addressT align = get_alignment(size);
  
  bss_alloc (symbolP, size, align);
  S_CLEAR_EXTERNAL (symbolP);

  return symbolP;
}

static addressT get_alignment(addressT size)
{
  SKIP_WHITESPACE ();

  if (*input_line_pointer == ',')
    {
      return parse_user_alignment();
    }
  
  return calculate_default_alignment(size);
}

static addressT parse_user_alignment(void)
{
  addressT align = parse_align (1);
  
  if (align == (addressT) -1)
    return 0;
    
  return align;
}

static addressT calculate_default_alignment(addressT size)
{
  const addressT ALIGN_8_BYTE = 3;
  const addressT ALIGN_4_BYTE = 2;
  const addressT ALIGN_2_BYTE = 1;
  const addressT ALIGN_1_BYTE = 0;
  const addressT SIZE_8_BYTE = 8;
  const addressT SIZE_4_BYTE = 4;
  const addressT SIZE_2_BYTE = 2;
  
  if (size >= SIZE_8_BYTE)
    return ALIGN_8_BYTE;
  if (size >= SIZE_4_BYTE)
    return ALIGN_4_BYTE;
  if (size >= SIZE_2_BYTE)
    return ALIGN_2_BYTE;
    
  return ALIGN_1_BYTE;
}

static void
arc_lcomm (int ignore)
{
  symbolS *symbolP = s_comm_internal (ignore, arc_lcomm_internal);

  if (symbolP)
    symbol_get_bfdsym (symbolP)->flags |= BSF_OBJECT;
}

/* Select the cpu we're assembling for.  */

static const char* get_cpu_name(const char* cpu)
{
    if (!strcmp("ARC600", cpu) || !strcmp("ARC601", cpu) || !strcmp("A6", cpu))
        return "arc600";
    if (!strcmp("ARC700", cpu) || !strcmp("A7", cpu))
        return "arc700";
    if (!strcmp("EM", cpu))
        return "arcem";
    if (!strcmp("HS", cpu))
        return "archs";
    if (!strcmp("NPS400", cpu))
        return "nps400";
    return cpu;
}

static void arc_option(int ignore ATTRIBUTE_UNUSED)
{
    char c;
    char *cpu;

    c = get_symbol_name(&cpu);
    
    const char *cpu_name = get_cpu_name(cpu);
    arc_select_cpu(cpu_name, MACH_SELECTION_FROM_CPU_DIRECTIVE);

    restore_line_pointer(c);
    demand_empty_rest_of_line();
}

/* Smartly print an expression.  */

static const char *get_operation_name(int op)
{
  switch (op)
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

static const char *get_md_name(int md)
{
  switch (md)
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

static const char *get_symbol_name_or_default(void *symbol)
{
  return symbol ? S_GET_NAME(symbol) : "--";
}

static void
debug_exp (expressionS *t)
{
  const char *name ATTRIBUTE_UNUSED;
  const char *namemd ATTRIBUTE_UNUSED;

  pr_debug ("debug_exp: ");

  name = get_operation_name(t->X_op);
  namemd = get_md_name(t->X_md);

  pr_debug ("%s (%s, %s, %d, %s)", name,
	    get_symbol_name_or_default(t->X_add_symbol),
	    get_symbol_name_or_default(t->X_op_symbol),
	    (int) t->X_add_number,
	    (t->X_md) ? namemd : "--");
  pr_debug ("\n");
  fflush (stderr);
}

/* Helper for parsing an argument, used for sorting out the relocation
   type.  */

static void
set_illegal_result(expressionS *resultP, const char *message)
{
  as_bad(_(message));
  resultP->X_op = O_illegal;
}

static const struct arc_reloc_op_tag *
find_relocation_operator(const char *reloc_name, size_t len)
{
  const struct arc_reloc_op_tag *r = &arc_reloc_op[0];
  int i;
  
  for (i = arc_num_reloc_op - 1; i >= 0; i--, r++)
    {
      if (len == r->length && memcmp(reloc_name, r->name, len) == 0)
        return r;
    }
  return NULL;
}

static int
parse_relocation_name(char **reloc_name, size_t *len, expressionS *resultP)
{
  char c;
  
  input_line_pointer++;
  c = get_symbol_name(reloc_name);
  *len = input_line_pointer - *reloc_name;
  
  if (*len == 0)
    {
      set_illegal_result(resultP, "No relocation operand");
      return 0;
    }
  
  restore_line_pointer(c);
  return 1;
}

static int
parse_tls_base(expressionS *resultP)
{
  char *sym_name, c;
  symbolS *base;
  
  if (resultP->X_op_symbol != NULL || resultP->X_op != O_symbol)
    {
      as_bad(_("Unable to parse TLS base: %s"), input_line_pointer);
      resultP->X_op = O_illegal;
      return 0;
    }
  
  input_line_pointer++;
  c = get_symbol_name(&sym_name);
  base = symbol_find_or_make(sym_name);
  resultP->X_op = O_subtract;
  resultP->X_op_symbol = base;
  restore_line_pointer(c);
  return 1;
}

static int
parse_complex_expression(const struct arc_reloc_op_tag *r, expressionS *right, expressionS *resultP)
{
  if (!r->complex_expr)
    {
      as_bad(_("@%s is not a complex relocation."), r->name);
      resultP->X_op = O_illegal;
      return 0;
    }
  
  expression(right);
  
  if (right->X_op != O_constant)
    {
      as_bad(_("Bad expression: @%s + %s."), r->name, input_line_pointer);
      resultP->X_op = O_illegal;
      return 0;
    }
  
  return 1;
}

static void
parse_reloc_symbol(expressionS *resultP)
{
  char *reloc_name;
  size_t len;
  const struct arc_reloc_op_tag *r;
  expressionS right;

  if (resultP->X_op != O_symbol)
    {
      set_illegal_result(resultP, "No valid label relocation operand");
      return;
    }

  if (!parse_relocation_name(&reloc_name, &len, resultP))
    return;

  r = find_relocation_operator(reloc_name, len);
  if (!r)
    {
      as_bad(_("Unknown relocation operand: @%s"), reloc_name);
      resultP->X_op = O_illegal;
      return;
    }

  SKIP_WHITESPACE();
  
  if (*input_line_pointer == '@')
    {
      if (!parse_tls_base(resultP))
        return;
      right.X_add_number = 0;
    }

  if (*input_line_pointer != '+' && *input_line_pointer != '-')
    {
      right.X_add_number = 0;
    }
  else
    {
      if (!parse_complex_expression(r, &right, resultP))
        return;
    }

  resultP->X_md = r->op;
  resultP->X_add_number = right.X_add_number;
}

/* Parse the arguments to an opcode.  */

static bool is_valid_state(bool saw_comma, bool saw_arg, int num_args, int ntok)
{
    return !(saw_comma || !saw_arg || num_args == ntok);
}

static bool should_error_on_arg(bool saw_arg, bool saw_comma, int num_args, int ntok)
{
    return (saw_arg && !saw_comma) || num_args == ntok;
}

static void handle_comma(bool *saw_comma, bool *saw_arg, bool *error)
{
    if (*saw_comma || !*saw_arg)
    {
        *error = true;
        return;
    }
    *saw_comma = true;
}

static void handle_closing_bracket(int *brk_lvl, expressionS **tok, int *num_args, 
                                  bool saw_arg, int ntok, bool *error)
{
    --(*brk_lvl);
    if (!saw_arg || *num_args == ntok)
    {
        *error = true;
        return;
    }
    (*tok)->X_op = O_bracket;
    ++(*tok);
    ++(*num_args);
}

static void handle_opening_bracket(int *brk_lvl, expressionS **tok, int *num_args, 
                                   int ntok, bool *error)
{
    if (*brk_lvl || *num_args == ntok)
    {
        *error = true;
        return;
    }
    ++(*brk_lvl);
    (*tok)->X_op = O_bracket;
    ++(*tok);
    ++(*num_args);
}

static void handle_colon(expressionS **tok, int *num_args, bool *saw_arg, 
                        bool saw_arg_val, int ntok, bool *error)
{
    if (!saw_arg_val || *num_args == ntok)
    {
        *error = true;
        return;
    }
    (*tok)->X_op = O_colon;
    *saw_arg = false;
    ++(*tok);
    ++(*num_args);
}

static void process_expression_token(expressionS *tok)
{
    tok->X_op = O_symbol;
    tok->X_md = O_absent;
    expression(tok);
    
    if (*input_line_pointer == '@')
        parse_reloc_symbol(tok);
        
    debug_exp(tok);
}

static void handle_at_symbol(expressionS **tok, int *num_args, bool *saw_comma, 
                             bool *saw_arg, bool saw_arg_val, bool saw_comma_val, 
                             int ntok, bool *error)
{
    if (should_error_on_arg(saw_arg_val, saw_comma_val, *num_args, ntok))
    {
        *error = true;
        return;
    }
    
    input_line_pointer++;
    process_expression_token(*tok);
    
    if ((*tok)->X_op == O_illegal || (*tok)->X_op == O_absent || *num_args == ntok)
    {
        *error = true;
        return;
    }
    
    *saw_comma = false;
    *saw_arg = true;
    (*tok)++;
    (*num_args)++;
}

static void process_default_token(expressionS *tok)
{
    tok->X_op = O_absent;
    tok->X_md = O_absent;
    expression(tok);
    
    if (*input_line_pointer == '@')
        parse_reloc_symbol(tok);
    else
        resolve_register(tok);
        
    debug_exp(tok);
}

static void handle_default(expressionS **tok, int *num_args, bool *saw_comma, 
                           bool *saw_arg, bool saw_arg_val, bool saw_comma_val,
                           int ntok, bool *error)
{
    if (should_error_on_arg(saw_arg_val, saw_comma_val, *num_args, ntok))
    {
        *error = true;
        return;
    }
    
    process_default_token(*tok);
    
    if ((*tok)->X_op == O_illegal || (*tok)->X_op == O_absent || *num_args == ntok)
    {
        *error = true;
        return;
    }
    
    *saw_comma = false;
    *saw_arg = true;
    (*tok)++;
    (*num_args)++;
}

static void report_error(int brk_lvl, bool saw_comma, bool saw_arg)
{
    if (brk_lvl)
        as_bad(_("Brackets in operand field incorrect"));
    else if (saw_comma)
        as_bad(_("extra comma"));
    else if (!saw_arg)
        as_bad(_("missing argument"));
    else
        as_bad(_("missing comma or colon"));
}

static int
tokenize_arguments(char *str,
                   expressionS *tok,
                   int ntok)
{
    char *old_input_line_pointer;
    bool saw_comma = false;
    bool saw_arg = false;
    bool error = false;
    int brk_lvl = 0;
    int num_args = 0;
    
    memset(tok, 0, sizeof(*tok) * ntok);
    
    old_input_line_pointer = input_line_pointer;
    input_line_pointer = str;
    
    while (*input_line_pointer && !error)
    {
        SKIP_WHITESPACE();
        switch (*input_line_pointer)
        {
        case '\0':
            goto fini;
            
        case ',':
            input_line_pointer++;
            handle_comma(&saw_comma, &saw_arg, &error);
            break;
            
        case '}':
        case ']':
            input_line_pointer++;
            handle_closing_bracket(&brk_lvl, &tok, &num_args, saw_arg, ntok, &error);
            break;
            
        case '{':
        case '[':
            input_line_pointer++;
            handle_opening_bracket(&brk_lvl, &tok, &num_args, ntok, &error);
            break;
            
        case ':':
            input_line_pointer++;
            handle_colon(&tok, &num_args, &saw_arg, saw_arg, ntok, &error);
            break;
            
        case '@':
            handle_at_symbol(&tok, &num_args, &saw_comma, &saw_arg, 
                           saw_arg, saw_comma, ntok, &error);
            break;
            
        case '%':
            ++input_line_pointer;
        default:
            handle_default(&tok, &num_args, &saw_comma, &saw_arg, 
                         saw_arg, saw_comma, ntok, &error);
            break;
        }
    }
    
fini:
    if (error || saw_comma || brk_lvl)
    {
        report_error(brk_lvl, saw_comma, saw_arg);
        input_line_pointer = old_input_line_pointer;
        return -1;
    }
    
    input_line_pointer = old_input_line_pointer;
    return num_args;
}

/* Parse the flags to a structure.  */

static int process_dot_separator(bool *saw_dot, bool *saw_flg)
{
    if (*saw_dot)
        return -1;
    *saw_dot = true;
    *saw_flg = false;
    return 0;
}

static int validate_flag_conditions(bool saw_flg, bool saw_dot, int num_flags, int nflg)
{
    if (saw_flg && !saw_dot)
        return -1;
    if (num_flags >= nflg)
        return -1;
    return 0;
}

static int extract_flag_name(char **input_ptr, struct arc_flags *flag)
{
    const char *valid_chars = "abcdefghijklmnopqrstuvwxyz0123456789";
    size_t flgnamelen = strspn(*input_ptr, valid_chars);
    
    if (flgnamelen > MAX_FLAG_NAME_LENGTH)
        return -1;
    
    memcpy(flag->name, *input_ptr, flgnamelen);
    *input_ptr += flgnamelen;
    return 0;
}

static void report_error(bool saw_dot, bool saw_flg)
{
    if (saw_dot)
        as_bad(_("extra dot"));
    else if (!saw_flg)
        as_bad(_("unrecognized flag"));
    else
        as_bad(_("failed to parse flags"));
}

static int process_flag_character(char **input_ptr, struct arc_flags **flags,
                                 bool *saw_dot, bool *saw_flg, 
                                 int *num_flags, int nflg)
{
    if (**input_ptr == '.')
    {
        (*input_ptr)++;
        return process_dot_separator(saw_dot, saw_flg);
    }
    
    if (is_end_of_stmt(**input_ptr) || is_whitespace(**input_ptr))
        return 1;
    
    if (validate_flag_conditions(*saw_flg, *saw_dot, *num_flags, nflg) < 0)
        return -1;
    
    if (extract_flag_name(input_ptr, *flags) < 0)
        return -1;
    
    (*flags)++;
    *saw_dot = false;
    *saw_flg = true;
    (*num_flags)++;
    return 0;
}

static int tokenize_flags(const char *str, struct arc_flags flags[], int nflg)
{
    char *old_input_line_pointer;
    bool saw_flg = false;
    bool saw_dot = false;
    int num_flags = 0;
    
    memset(flags, 0, sizeof(*flags) * nflg);
    
    old_input_line_pointer = input_line_pointer;
    input_line_pointer = (char *)str;
    
    while (*input_line_pointer)
    {
        int result = process_flag_character(&input_line_pointer, &flags,
                                           &saw_dot, &saw_flg, 
                                           &num_flags, nflg);
        if (result < 0)
        {
            report_error(saw_dot, saw_flg);
            input_line_pointer = old_input_line_pointer;
            return -1;
        }
        if (result > 0)
            break;
    }
    
    input_line_pointer = old_input_line_pointer;
    return num_flags;
}

/* Apply the fixups in order.  */

static int calculate_fixup_size(const struct arc_insn *insn, const struct arc_fixup *fixup)
{
    return ((insn->len == 2) && !fixup->islong) ? 2 : 4;
}

static int calculate_fixup_offset(const struct arc_insn *insn, const struct arc_fixup *fixup)
{
    return fixup->islong ? insn->len : 0;
}

static void validate_reloc(const struct arc_fixup *fixup)
{
    if (fixup->reloc == 0)
        as_fatal(_("Unhandled reloc type"));
}

static int get_pcrel_flag(const struct arc_fixup *fixup)
{
    if ((int)fixup->reloc < 0)
        return fixup->pcrel;
    
    reloc_howto_type *reloc_howto = bfd_reloc_type_lookup(stdoutput, fixup->reloc);
    gas_assert(reloc_howto);
    return reloc_howto->pc_relative;
}

static const char* get_reloc_type_name(const struct arc_fixup *fixup)
{
    return (fixup->reloc < 0) ? "Internal" : bfd_get_reloc_code_name(fixup->reloc);
}

static void log_fixup_debug(fragS *fragP, const struct arc_fixup *fixup, 
                           int pcrel, int size, int fix, int offset)
{
    pr_debug("%s:%d: apply_fixups: new %s fixup (PCrel:%s) of size %d @ offset %d + %d\n",
             fragP->fr_file, fragP->fr_line,
             get_reloc_type_name(fixup),
             pcrel ? "Y" : "N",
             size, fix, offset);
}

static void update_zol_symbol(const struct arc_insn *insn, const struct arc_fixup *fixup)
{
    if (LP_INSN(insn->insn))
    {
        gas_assert(fixup->exp.X_add_symbol);
        ARC_SET_FLAG(fixup->exp.X_add_symbol, ARC_FLAG_ZOL);
    }
}

static void process_single_fixup(const struct arc_insn *insn, 
                                const struct arc_fixup *fixup,
                                fragS *fragP, int fix)
{
    int size = calculate_fixup_size(insn, fixup);
    int offset = calculate_fixup_offset(insn, fixup);
    
    validate_reloc(fixup);
    int pcrel = get_pcrel_flag(fixup);
    
    log_fixup_debug(fragP, fixup, pcrel, size, fix, offset);
    
    fix_new_exp(fragP, fix + offset, size, &fixup->exp, pcrel, fixup->reloc);
    
    update_zol_symbol(insn, fixup);
}

static void apply_fixups(struct arc_insn *insn, fragS *fragP, int fix)
{
    int i;
    for (i = 0; i < insn->nfixups; i++)
    {
        process_single_fixup(insn, &insn->fixups[i], fragP, fix);
    }
}

/* Actually output an instruction with its fixup.  */

static void write_instruction_bytes(char *f, struct arc_insn *insn)
{
    md_number_to_chars_midend(f, insn->insn, insn->len);
    
    if (insn->has_limm)
        md_number_to_chars_midend(f + insn->len, insn->limm, 4);
}

static void log_instruction_details(struct arc_insn *insn)
{
    pr_debug("Emit insn : 0x%llx\n", insn->insn);
    pr_debug("\tLength  : %d\n", insn->len);
    pr_debug("\tLong imm: 0x%lx\n", insn->limm);
}

static size_t calculate_total_length(struct arc_insn *insn)
{
    const size_t LIMM_SIZE = 4;
    return insn->len + (insn->has_limm ? LIMM_SIZE : 0);
}

static void emit_insn0(struct arc_insn *insn, char *where, bool relax)
{
    char *f = where;
    size_t total_len;

    log_instruction_details(insn);

    total_len = calculate_total_length(insn);
    
    if (!relax)
        f = frag_more(total_len);

    write_instruction_bytes(f, insn);
    dwarf2_emit_insn(total_len);

    if (!relax)
        apply_fixups(insn, frag_now, (f - frag_now->fr_literal));
}

static void copy_arc_relax_data(struct arc_relax_type *dest, 
                                 const struct arc_relax_type *src)
{
    memcpy(dest, src, sizeof(struct arc_relax_type));
}

static void handle_insufficient_frag_room(relax_substateT subtype, symbolS *s)
{
    struct arc_relax_type relax_info_copy;
    
    copy_arc_relax_data(&relax_info_copy, &frag_now->tc_frag_data);
    
    frag_wane(frag_now);
    frag_grow(FRAG_MAX_GROWTH);
    
    copy_arc_relax_data(&frag_now->tc_frag_data, &relax_info_copy);
    
    frag_var(rs_machine_dependent, FRAG_MAX_GROWTH, 0, subtype, s, 0, 0);
}

static void emit_insn1(struct arc_insn *insn)
{
    symbolS *s = make_expr_symbol(&insn->fixups[0].exp);
    frag_now->tc_frag_data.pcrel = insn->fixups[0].pcrel;

    if (frag_room() < FRAG_MAX_GROWTH)
    {
        handle_insufficient_frag_room(frag_now->fr_subtype, s);
    }
    else
    {
        frag_var(rs_machine_dependent, FRAG_MAX_GROWTH, 0,
                 frag_now->fr_subtype, s, 0, 0);
    }
}

static void
emit_insn (struct arc_insn *insn)
{
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

  return !contains_register (ex->X_add_symbol) && !contains_register (ex->X_op_symbol);
}

/* Returns the register number within a symbol.  */

static int
get_register (symbolS *sym)
{
  if (!contains_register (sym))
    return -1;

  expressionS *ex = symbol_get_value_expression (sym);
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

  while (ntok >= cidx)
  {
    memcpy (&tok[ntok+1], &tok[ntok], sizeof (*tok));
    if (cidx == ntok)
      return 1;
    ntok--;
  }
  
  return 0;
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

  #define NUM_FEATURE_CHECKS (sizeof(feature_checks) / sizeof(feature_checks[0]))

  for (size_t i = 0; i < NUM_FEATURE_CHECKS; i++) {
    if (feature_checks[i].check_func(sc) && 
        !(selected_cpu.features & feature_checks[i].feature_flag)) {
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

static bool is_implicit_flag_class(const struct arc_flag_class *cl_flags)
{
    return cl_flags->flag_class & F_CLASS_IMPLICIT;
}

static bool is_extension_flag_class(const struct arc_flag_class *cl_flags)
{
    return cl_flags->flag_class & F_CLASS_EXTEND;
}

static bool is_required_flag_class(const struct arc_flag_class *cl_flags)
{
    return cl_flags->flag_class & F_CLASS_REQUIRED;
}

static bool is_optional_flag_class(const struct arc_flag_class *cl_flags)
{
    return cl_flags->flag_class & F_CLASS_OPTIONAL;
}

static void initialize_flags(struct arc_flags *first_pflag, int nflgs)
{
    int i;
    for (i = 0; i < nflgs; i++)
        first_pflag[i].flgp = NULL;
}

static bool match_flag_name(struct arc_flags *pflag, int nflgs, 
                           const char *name, 
                           const void *flag_operand,
                           int *remaining_flags)
{
    int i;
    for (i = 0; i < nflgs; i++, pflag++)
    {
        if (strcmp(name, pflag->name) == 0)
        {
            if (pflag->flgp != NULL)
                return false;
            pflag->flgp = flag_operand;
            (*remaining_flags)--;
            return true;
        }
    }
    return true;
}

static int process_extension_conditionals(struct arc_flags *first_pflag, 
                                         int nflgs, 
                                         int *remaining_flags)
{
    struct arc_flag_operand *pf = ext_condcode.arc_ext_condcode;
    int matches = 0;
    
    while (pf->name)
    {
        if (!match_flag_name(first_pflag, nflgs, pf->name, pf, remaining_flags))
            return -1;
        if (*remaining_flags < nflgs)
            matches++;
        pf++;
    }
    return matches;
}

static int process_flag_operands(const struct arc_flag_class *cl_flags,
                                struct arc_flags *first_pflag,
                                int nflgs,
                                int *remaining_flags)
{
    const unsigned *flgopridx;
    int matches = 0;
    
    for (flgopridx = cl_flags->flags; *flgopridx; ++flgopridx)
    {
        const struct arc_flag_operand *flg_operand = &arc_flag_operands[*flgopridx];
        if (!match_flag_name(first_pflag, nflgs, flg_operand->name, 
                           flg_operand, remaining_flags))
            return -1;
        if (*remaining_flags < nflgs)
            matches++;
    }
    return matches;
}

static bool validate_flag_matches(const struct arc_flag_class *cl_flags, 
                                 int cl_matches)
{
    if (is_required_flag_class(cl_flags) && cl_matches == 0)
        return false;
    if (is_optional_flag_class(cl_flags) && cl_matches > 1)
        return false;
    return true;
}

static bool
parse_opcode_flags (const struct arc_opcode *opcode,
                    int nflgs,
                    struct arc_flags *first_pflag)
{
    int remaining_flags;
    const unsigned char *flgidx;

    remaining_flags = nflgs;
    initialize_flags(first_pflag, nflgs);

    for (flgidx = opcode->flags; *flgidx; ++flgidx)
    {
        const struct arc_flag_class *cl_flags = &arc_flag_classes[*flgidx];
        int cl_matches = 0;

        if (is_implicit_flag_class(cl_flags))
            continue;

        if (ext_condcode.arc_ext_condcode && is_extension_flag_class(cl_flags))
        {
            cl_matches = process_extension_conditionals(first_pflag, nflgs, 
                                                       &remaining_flags);
            if (cl_matches < 0)
                return false;
        }

        int operand_matches = process_flag_operands(cl_flags, first_pflag, 
                                                   nflgs, &remaining_flags);
        if (operand_matches < 0)
            return false;
        cl_matches += operand_matches;

        if (!validate_flag_matches(cl_flags, cl_matches))
            return false;
    }

    return remaining_flags == 0;
}


/* Search forward through all variants of an opcode looking for a
   syntax match.  */

static int check_architecture_match(const struct arc_opcode *opcode)
{
    return (opcode->cpu & selected_cpu.flags) && check_cpu_feature(opcode->subclass);
}

static int check_operand_count(int tokidx, int ntok)
{
    return tokidx < ntok;
}

static int handle_address_type_operand(const struct arc_operand *operand, 
                                      expressionS *tok, 
                                      int tokidx, 
                                      const char **tmpmsg)
{
    if (tok[tokidx].X_op != O_addrtype)
        return 0;
    
    gas_assert(operand->insert != NULL);
    *tmpmsg = NULL;
    (*operand->insert)(0, tok[tokidx].X_add_number, tmpmsg);
    return *tmpmsg == NULL;
}

static int check_duplicate_operand(const struct arc_operand *operand,
                                  const expressionS *t,
                                  expressionS *tok,
                                  int tokidx)
{
    if (!(operand->flags & ARC_OPERAND_DUPLICATE))
        return 1;
        
    if (t->X_op != O_register || !is_ir_num(t->X_add_number) ||
        (regno(t->X_add_number) != regno(tok[tokidx].X_add_number)))
        return 0;
        
    return 1;
}

static int handle_register_operand(const struct arc_operand *operand,
                                  expressionS *tok,
                                  int tokidx,
                                  int *ntok,
                                  const expressionS *t,
                                  const char **tmpmsg)
{
    if ((tok[tokidx].X_op != O_register || !is_ir_num(tok[tokidx].X_add_number)) &&
        !(operand->flags & ARC_OPERAND_IGNORE))
        return 0;
    
    if (!check_duplicate_operand(operand, t, tok, tokidx))
        return 0;
    
    if (operand->insert)
    {
        *tmpmsg = NULL;
        (*operand->insert)(0, regno(tok[tokidx].X_add_number), tmpmsg);
        if (*tmpmsg)
        {
            if (operand->flags & ARC_OPERAND_IGNORE)
            {
                if (!allocate_tok(tok, *ntok - 1, tokidx))
                    return 0;
                tok[tokidx].X_op = O_absent;
                ++(*ntok);
            }
            else
                return 0;
        }
    }
    return 1;
}

static int check_bracket_operand(expressionS *tok, int tokidx)
{
    return tok[tokidx].X_op == O_bracket;
}

static int check_colon_operand(expressionS *tok, int tokidx)
{
    return tok[tokidx].X_op == O_colon;
}

static void convert_aux_register_symbol(expressionS *tok, int tokidx)
{
    const char *p = S_GET_NAME(tok[tokidx].X_add_symbol);
    char *tmpp = strdup(p);
    char *pp;
    
    for (pp = tmpp; *pp; ++pp)
        *pp = TOLOWER(*pp);
    
    const struct arc_aux_reg *auxr = str_hash_find(arc_aux_hash, tmpp);
    if (auxr)
    {
        tok[tokidx].X_op = O_constant;
        tok[tokidx].X_add_number = auxr->address;
        ARC_SET_FLAG(tok[tokidx].X_add_symbol, ARC_FLAG_AUX);
    }
    free(tmpp);
}

static int check_immediate_range(const struct arc_operand *operand,
                                offsetT val,
                                const char **tmpmsg)
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
    return 1;
}

#define ALIGNMENT_32BIT 0x03
#define ALIGNMENT_16BIT 0x01

static int check_immediate_alignment(const struct arc_operand *operand,
                                    offsetT val,
                                    const char **tmpmsg)
{
    if ((operand->flags & ARC_OPERAND_ALIGNED32) && (val & ALIGNMENT_32BIT))
    {
        *tmpmsg = _("immediate is not 32bit aligned");
        return 0;
    }
    
    if ((operand->flags & ARC_OPERAND_ALIGNED16) && (val & ALIGNMENT_16BIT))
    {
        *tmpmsg = _("immediate is not 16bit aligned");
        return 0;
    }
    return 1;
}

static int handle_constant_operand(const struct arc_operand *operand,
                                  expressionS *tok,
                                  int tokidx,
                                  const char **tmpmsg)
{
    offsetT val = tok[tokidx].X_add_number;
    
    if (operand->bits != 32 && !(operand->flags & ARC_OPERAND_NCHK))
    {
        if (!check_immediate_range(operand, val, tmpmsg))
            return 0;
        if (!check_immediate_alignment(operand, val, tmpmsg))
            return 0;
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

static int handle_register_range(const struct arc_operand *operand,
                                expressionS *tok,
                                int tokidx,
                                const char **tmpmsg)
{
    if (tok[tokidx].X_add_number != 0 ||
        !contains_register(tok[tokidx].X_add_symbol) ||
        !contains_register(tok[tokidx].X_op_symbol))
        return 0;
    
    int regs = get_register(tok[tokidx].X_add_symbol);
    regs <<= 16;
    regs |= get_register(tok[tokidx].X_op_symbol);
    
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

static int handle_relocation_operand(const struct arc_operand *operand,
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
        if (!generic_reloc_p(operand->default_reloc))
            return 0;
        break;
    default:
        break;
    }
    return 1;
}

static int handle_bracket_for_ignored_operand(const struct arc_operand *operand,
                                             expressionS *tok,
                                             int tokidx,
                                             int *ntok)
{
    if (!(operand->flags & ARC_OPERAND_IGNORE))
        return 0;
    
    if (!allocate_tok(tok, *ntok - 1, tokidx))
        return 0;
    
    tok[tokidx].X_op = O_absent;
    ++(*ntok);
    return 1;
}

static int handle_symbol_operand(const struct arc_opcode *opcode,
                                const struct arc_operand *operand,
                                expressionS *tok,
                                int tokidx,
                                int *ntok,
                                const expressionS *t,
                                const char **tmpmsg)
{
    if (opcode->insn_class == AUXREG)
        convert_aux_register_symbol(tok, tokidx);
    
    if (tok[tokidx].X_op == O_constant)
        return handle_constant_operand(operand, tok, tokidx, tmpmsg);
    
    return handle_relocation_operand(operand, tok, tokidx);
}

static int check_final_duplicate(const struct arc_operand *operand,
                                const expressionS *t,
                                expressionS *tok,
                                int tokidx,
                                const char **tmpmsg)
{
    if (!(operand->flags & ARC_OPERAND_DUPLICATE))
        return 1;
    
    if (t->X_op == O_illegal || t->X_op == O_absent ||
        t->X_op == O_register ||
        (t->X_add_number != tok[tokidx].X_add_number))
    {
        *tmpmsg = _("operand is not duplicate of the previous one");
        return 0;
    }
    return 1;
}

static int handle_numeric_operand(const struct arc_opcode *opcode,
                                 const struct arc_operand *operand,
                                 expressionS *tok,
                                 int tokidx,
                                 int *ntok,
                                 const expressionS *t,
                                 const char **tmpmsg)
{
    switch (tok[tokidx].X_op)
    {
    case O_illegal:
    case O_absent:
    case O_register:
        return 0;
    
    case O_bracket:
        return handle_bracket_for_ignored_operand(operand, tok, tokidx, ntok);
    
    case O_symbol:
        return handle_symbol_operand(opcode, operand, tok, tokidx, ntok, t, tmpmsg);
    
    case O_constant:
        return handle_constant_operand(operand, tok, tokidx, tmpmsg);
    
    case O_subtract:
        if (handle_register_range(operand, tok, tokidx, tmpmsg))
            return 1;
        return handle_relocation_operand(operand, tok, tokidx);
    
    default:
        return handle_relocation_operand(operand, tok, tokidx);
    }
}

static int match_single_operand(const struct arc_opcode *opcode,
                               const struct arc_operand *operand,
                               expressionS *tok,
                               int tokidx,
                               int *ntok,
                               const expressionS **t,
                               const char **tmpmsg)
{
    int result = 0;
    
    switch (operand->flags & ARC_OPERAND_TYPECHECK_MASK)
    {
    case ARC_OPERAND_ADDRTYPE:
        result = handle_address_type_operand(operand, tok, tokidx, tmpmsg);
        break;
    
    case ARC_OPERAND_IR:
        result = handle_register_operand(operand, tok, tokidx, ntok, *t, tmpmsg);
        if (result)
            *t = &tok[tokidx];
        break;
    
    case ARC_OPERAND_BRAKET:
        result = check_bracket_operand(tok, tokidx);
        break;
    
    case ARC_OPERAND_COLON:
        result = check_colon_operand(tok, tokidx);
        break;
    
    case ARC_OPERAND_LIMM:
    case ARC_OPERAND_SIGNED:
    case ARC_OPERAND_UNSIGNED:
        result = handle_numeric_operand(opcode, operand, tok, tokidx, ntok, *t, tmpmsg);
        if (result && !check_final_duplicate(operand, *t, tok, tokidx, tmpmsg))
            result = 0;
        if (result)
            *t = &tok[tokidx];
        break;
    
    default:
        abort();
    }
    
    return result;
}

static const struct arc_opcode *
try_match_opcode(const struct arc_opcode *opcode,
                expressionS *tok,
                int *ntok,
                struct arc_flags *first_pflag,
                int nflgs,
                const char **tmpmsg)
{
    const unsigned char *opidx;
    int tokidx = 0;
    expressionS emptyE;
    const expressionS *t;
    
    memset(&emptyE, 0, sizeof(emptyE));
    t = &emptyE;
    
    pr_debug("%s:%d: find_opcode_match: trying opcode 0x%08llX ",
            frag_now->fr_file, frag_now->fr_line, opcode->opcode);
    
    if (!check_architecture_match(opcode))
        return NULL;
    
    pr_debug("cpu ");
    
    for (opidx = opcode->operands; *opidx; ++opidx)
    {
        const struct arc_operand *operand = &arc_operands[*opidx];
        
        if (ARC_OPERAND_IS_FAKE(operand))
            continue;
        
        if (!check_operand_count(tokidx, *ntok))
            return NULL;
        
        if (!match_single_operand(opcode, operand, tok, tokidx, ntok, &t, tmpmsg))
            return NULL;
        
        ++tokidx;
    }
    
    pr_debug("opr ");
    
    if (!parse_opcode_flags(opcode, nflgs, first_pflag))
    {
        *tmpmsg = _("flag mismatch");
        return NULL;
    }
    
    pr_debug("flg");
    
    if (tokidx == *ntok)
    {
        pr_debug("\n");
        return opcode;
    }
    
    *tmpmsg = _("too many arguments");
    pr_debug("\n");
    return NULL;
}

static const struct arc_opcode *
find_opcode_match(const struct arc_opcode_hash_entry *entry,
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
    const char *tmpmsg = NULL;
    
    arc_opcode_hash_entry_iterator_init(&iter);
    memcpy(bktok, tok, MAX_INSN_ARGS * sizeof(*tok));
    bkntok = ntok;
    
    for (opcode = arc_opcode_hash_entry_iterator_next(entry, &iter);
         opcode != NULL;
         opcode = arc_opcode_hash_entry_iterator_next(entry, &iter))
    {
        const struct arc_opcode *result;
        int tokidx_before = ntok;
        
        result = try_match_opcode(opcode, tok, &ntok, first_pflag, nflgs, &tmpmsg);
        
        if (check_architecture_match(opcode))
            got_cpu_match = 1;
        
        if (result)
        {
            *pntok = ntok;
            return result;
        }
        
        memcpy(tok, bktok, MAX_INSN_ARGS * sizeof(*tok));
        ntok = bkntok;
        
        if (tokidx_before >= maxerridx && tmpmsg)
        {
            maxerridx = tokidx_before;
            *errmsg = tmpmsg;
        }
    }
    
    if (*pcpumatch)
        *pcpumatch = got_cpu_match;
    
    return NULL;
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

static bool is_limm_operand(const struct arc_operand *operand)
{
    return operand->bits == 32 && (operand->flags & ARC_OPERAND_LIMM);
}

static bool is_valid_symbol_operand(const struct arc_operand *operand)
{
    return (operand->flags & ARC_OPERAND_LIMM) ||
           ((operand->flags & ARC_OPERAND_SIGNED) && operand->bits == 9);
}

static void calculate_range(const struct arc_operand *operand, offsetT *min, offsetT *max)
{
    if (operand->flags & ARC_OPERAND_SIGNED)
    {
        *max = (1 << (operand->bits - 1)) - 1;
        *min = -(1 << (operand->bits - 1));
    }
    else
    {
        *max = (1 << operand->bits) - 1;
        *min = 0;
    }
}

static bool is_value_in_range(const struct arc_operand *operand, offsetT val)
{
    offsetT min, max;
    calculate_range(operand, &min, &max);
    return min <= val && val <= max;
}

static bool match_constant_operand(const expressionS *tok,
                                  const struct arc_operand_operation *op,
                                  const struct arc_operand *operand)
{
    if (is_limm_operand(operand))
        return true;
    
    if (!(operand->flags & ARC_OPERAND_IR))
    {
        offsetT val = tok->X_add_number + op->count;
        return is_value_in_range(operand, val);
    }
    
    return false;
}

static bool match_symbol_operand(const struct arc_operand *operand)
{
    return is_valid_symbol_operand(operand);
}

static bool match_register_operand(const struct arc_operand *operand)
{
    return operand->flags & ARC_OPERAND_IR;
}

static bool match_bracket_operand(const struct arc_operand *operand)
{
    return operand->flags & ARC_OPERAND_BRAKET;
}

static bool
pseudo_operand_match (const expressionS *tok,
                     const struct arc_operand_operation *op)
{
    const struct arc_operand *operand_real = &arc_operands[op->operand_idx];
    
    switch (tok->X_op)
    {
    case O_constant:
        return match_constant_operand(tok, op, operand_real);
        
    case O_symbol:
        return match_symbol_operand(operand_real);
        
    case O_register:
        return match_register_operand(operand_real);
        
    case O_bracket:
        return match_bracket_operand(operand_real);
        
    default:
        return false;
    }
}

/* Find pseudo instruction in array.  */

static const struct arc_pseudo_insn *
find_matching_pseudo_insn(const struct arc_pseudo_insn *pseudo_insn,
                         int ntok,
                         const expressionS *tok)
{
  const struct arc_operand_operation *op = pseudo_insn->operand;
  int j;
  
  for (j = 0; j < ntok; ++j)
    if (!pseudo_operand_match(&tok[j], &op[j]))
      return NULL;
  
  return pseudo_insn;
}

static const struct arc_pseudo_insn *
find_pseudo_insn(const char *opname,
                int ntok,
                const expressionS *tok)
{
  const struct arc_pseudo_insn *pseudo_insn;
  unsigned int i;
  
  for (i = 0; i < arc_num_pseudo_insn; ++i)
    {
      pseudo_insn = &arc_pseudo_insns[i];
      if (strcmp(pseudo_insn->mnemonic_p, opname) != 0)
        continue;
      
      pseudo_insn = find_matching_pseudo_insn(pseudo_insn, ntok, tok);
      if (pseudo_insn != NULL)
        return pseudo_insn;
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

  pseudo_insn = find_pseudo_insn (opname, *ntok, tok);

  if (pseudo_insn == NULL)
    return NULL;

  if (pseudo_insn->flag_r != NULL)
    *nflgs += tokenize_flags (pseudo_insn->flag_r, &pflags[*nflgs],
			      MAX_INSN_FLGS - *nflgs);

  process_pseudo_operands(pseudo_insn, ntok, tok);
  swap_operands_if_needed(pseudo_insn, tok);

  return arc_find_opcode (pseudo_insn->mnemonic_r);
}

static void
process_pseudo_operands(const struct arc_pseudo_insn *pseudo_insn,
                        int *ntok,
                        expressionS *tok)
{
  unsigned i;

  for (i = 0; i < pseudo_insn->operand_cnt; ++i)
    {
      process_single_operand(&pseudo_insn->operand[i], &tok[i], ntok);
    }
}

static void
process_single_operand(const struct arc_operand_operation *operand_pseudo,
                       expressionS *tok_item,
                       int *ntok)
{
  const struct arc_operand *operand_real = &arc_operands[operand_pseudo->operand_idx];

  if (operand_real->flags & ARC_OPERAND_BRAKET && !operand_pseudo->needs_insert)
    return;

  if (operand_pseudo->needs_insert)
    {
      insert_operand(operand_pseudo, operand_real, tok_item, ntok);
    }
  else if (operand_pseudo->count)
    {
      adjust_operand_value(tok_item, operand_pseudo->count);
    }
}

static void
insert_operand(const struct arc_operand_operation *operand_pseudo,
               const struct arc_operand *operand_real,
               expressionS *tok_item,
               int *ntok)
{
  char construct_operand[MAX_CONSTR_STR];

  if (operand_real->flags & ARC_OPERAND_BRAKET)
    {
      tok_item->X_op = O_bracket;
      ++(*ntok);
      return;
    }

  construct_operand_string(construct_operand, operand_real->flags, operand_pseudo->count);
  tokenize_arguments (construct_operand, tok_item, 1);
  ++(*ntok);
}

static void
construct_operand_string(char *buffer,
                         unsigned int flags,
                         int count)
{
  if (flags & ARC_OPERAND_IR)
    snprintf (buffer, MAX_CONSTR_STR, "r%d", count);
  else
    snprintf (buffer, MAX_CONSTR_STR, "%d", count);
}

static void
adjust_operand_value(expressionS *tok_item,
                     int adjustment)
{
  if (tok_item->X_op == O_constant)
    tok_item->X_add_number += adjustment;
}

static void
swap_operands_if_needed(const struct arc_pseudo_insn *pseudo_insn,
                        expressionS *tok)
{
  unsigned i;

  for (i = 0; i < pseudo_insn->operand_cnt; ++i)
    {
      const struct arc_operand_operation *operand_pseudo = &pseudo_insn->operand[i];

      if (operand_pseudo->swap_operand_idx == i)
        continue;

      swap_operand (tok, i, operand_pseudo->swap_operand_idx);
      break;
    }
}

static const struct arc_opcode_hash_entry *
find_special_case_flag (const char *opname,
			int *nflgs,
			struct arc_flags *pflags)
{
  unsigned int i;

  for (i = 0; i < arc_num_flag_special; i++)
    {
      const struct arc_opcode_hash_entry *result = 
        check_special_case_instruction(opname, nflgs, pflags, i);
      if (result != NULL)
        return result;
    }
  return NULL;
}

static const struct arc_opcode_hash_entry *
check_special_case_instruction(const char *opname,
                               int *nflgs,
                               struct arc_flags *pflags,
                               unsigned int special_case_idx)
{
  const struct arc_flag_special *arc_flag_special_opcode;
  size_t oplen;

  arc_flag_special_opcode = &arc_flag_special_cases[special_case_idx];
  oplen = strlen(arc_flag_special_opcode->name);

  if (strncmp(opname, arc_flag_special_opcode->name, oplen) != 0)
    return NULL;

  return check_instruction_flags(opname + oplen, nflgs, pflags, 
                                 arc_flag_special_opcode);
}

static const struct arc_opcode_hash_entry *
check_instruction_flags(const char *remaining_opname,
                        int *nflgs,
                        struct arc_flags *pflags,
                        const struct arc_flag_special *arc_flag_special_opcode)
{
  unsigned flag_arr_idx;

  for (flag_arr_idx = 0;; ++flag_arr_idx)
    {
      unsigned flag_idx = arc_flag_special_opcode->flags[flag_arr_idx];
      if (flag_idx == 0)
        break;

      const struct arc_opcode_hash_entry *result = 
        process_matching_flag(remaining_opname, nflgs, pflags,
                             flag_idx, arc_flag_special_opcode->name);
      if (result != NULL)
        return result;
    }
  return NULL;
}

static const struct arc_opcode_hash_entry *
process_matching_flag(const char *remaining_opname,
                     int *nflgs,
                     struct arc_flags *pflags,
                     unsigned flag_idx,
                     const char *special_opcode_name)
{
  const char *flagnm = arc_flag_operands[flag_idx].name;
  size_t flaglen = strlen(flagnm);

  if (strcmp(remaining_opname, flagnm) != 0)
    return NULL;

  if (*nflgs + 1 > MAX_INSN_FLGS)
    return NULL;

  add_flag_to_list(pflags, nflgs, flagnm, flaglen);
  return arc_find_opcode(special_opcode_name);
}

static void
add_flag_to_list(struct arc_flags *pflags,
                int *nflgs,
                const char *flagnm,
                size_t flaglen)
{
  memcpy(pflags[*nflgs].name, flagnm, flaglen);
  pflags[*nflgs].name[flaglen] = '\0';
  (*nflgs)++;
}

/* Used to find special case opcode.  */

static const struct arc_opcode_hash_entry *
find_special_case (const char *opname,
		   int *nflgs,
		   struct arc_flags *pflags,
		   expressionS *tok,
		   int *ntok)
{
  const struct arc_opcode_hash_entry *entry;

  entry = find_special_case_pseudo (opname, ntok, tok, nflgs, pflags);

  if (entry == NULL)
    entry = find_special_case_flag (opname, nflgs, pflags);

  return entry;
}

/* Autodetect cpu attribute list.  */

static void update_feature_flags(const struct arc_opcode *opcode)
{
    unsigned i;
    for (i = 0; i < ARRAY_SIZE(feature_list); i++)
        if (opcode->subclass == feature_list[i].feature)
            selected_cpu.features |= feature_list[i].feature;
}

static void update_mpy_option(const struct arc_opcode *opcode)
{
    struct mpy_type {
        unsigned feature;
        unsigned encoding;
    } mpy_list[] = {{MPY1E, 1}, {MPY6E, 6}, {MPY7E, 7}, {MPY8E, 8}, {MPY9E, 9}};
    
    unsigned i;
    for (i = 0; i < ARRAY_SIZE(mpy_list); i++)
        if (opcode->subclass == mpy_list[i].feature)
            mpy_option = mpy_list[i].encoding;
}

static void process_token_md_type(const expressionS *tok)
{
    switch (tok->X_md) {
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
}

static void process_token_operator(const expressionS *tok)
{
    #define RF16_MIN_SPECIAL_REG 4
    #define RF16_MAX_SPECIAL_REG_LOW 9
    #define RF16_MIN_SPECIAL_REG_HIGH 16
    #define RF16_MAX_SPECIAL_REG_HIGH 25
    
    if (tok->X_op == O_register) {
        int reg_num = tok->X_add_number;
        if ((reg_num >= RF16_MIN_SPECIAL_REG && reg_num <= RF16_MAX_SPECIAL_REG_LOW) ||
            (reg_num >= RF16_MIN_SPECIAL_REG_HIGH && reg_num <= RF16_MAX_SPECIAL_REG_HIGH))
            rf16_only = false;
    }
}

static void autodetect_attributes(const struct arc_opcode *opcode,
                                 const expressionS *tok,
                                 int ntok)
{
    update_feature_flags(opcode);
    update_mpy_option(opcode);
    
    unsigned i;
    for (i = 0; i < (unsigned)ntok; i++) {
        process_token_md_type(&tok[i]);
        process_token_operator(&tok[i]);
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
  bool found_something = false;
  const struct arc_opcode_hash_entry *entry;
  int cpumatch = 1;
  const char *errmsg = NULL;

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
  found_something = true;
  
  const struct arc_opcode *opcode = find_opcode_match (entry, tok, &ntok, pflags,
						       nflgs, &cpumatch, &errmsg);
  
  if (opcode == NULL)
    {
      if (cpumatch)
	{
	  if (errmsg)
	    as_bad (_("%s for instruction '%s'"), errmsg, opname);
	  else
	    as_bad (_("inappropriate arguments for opcode '%s'"), opname);
	}
      else
	{
	  as_bad (_("opcode '%s' not supported for target %s"), opname,
		  selected_cpu.name);
	}
      return;
    }

  struct arc_insn insn;
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

  str = skip_to_whitespace_or_end (str + opnamelen);

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

static char *
skip_to_whitespace_or_end (char *str)
{
  while (!is_end_of_stmt (*str) && !is_whitespace (*str))
    str++;
  return str;
}

/* Callback to insert a register into the hash table.  */

static void
declare_register (const char *name, int number)
{
  symbolS *regS = symbol_create (name, reg_section,
				 &zero_address_frag, number);

  if (str_hash_insert (arc_reg_hash, S_GET_NAME (regS), regS, 0) != NULL)
    as_fatal (_("duplicate %s"), name);
}

/* Construct symbols for each of the general registers.  */

static void declare_single_register(int index) {
    char name[32];
    sprintf(name, "r%d", index);
    declare_register(name, index);
}

static void declare_register_pair(int index) {
    char name[32];
    sprintf(name, "r%dr%d", index, index + 1);
    declare_register(name, index);
}

static int is_even(int value) {
    return (value & 0x01) == 0;
}

static void declare_register_set(void) {
    const int MAX_REGISTERS = 64;
    
    for (int i = 0; i < MAX_REGISTERS; ++i) {
        declare_single_register(i);
        
        if (is_even(i)) {
            declare_register_pair(i);
        }
    }
}

/* Construct a symbol for an address type.  */

static void
declare_addrtype (const char *name, int number)
{
  symbolS *addrtypeS = symbol_create (name, undefined_section,
                                      &zero_address_frag, number);

  if (str_hash_insert (arc_addrtype_hash, S_GET_NAME (addrtypeS), addrtypeS, 0))
    as_fatal (_("duplicate %s"), name);
}

/* Port-specific assembler initialization.  This function is called
   once, at assembler startup time.  */

void initialize_cpu_and_architecture(void)
{
  if (mach_selection_mode == MACH_SELECTION_NONE)
    arc_select_cpu (TARGET_WITH_CPU, MACH_SELECTION_FROM_DEFAULT);

  target_big_endian = byte_order == BIG_ENDIAN;

  if (!bfd_set_arch_mach (stdoutput, bfd_arch_arc, selected_cpu.mach))
    as_warn (_("could not set architecture and machine"));

  bfd_set_private_flags (stdoutput, selected_cpu.eflags);
}

void initialize_opcode_hash_table(void)
{
  const struct arc_opcode *opcode = arc_opcodes;
  
  arc_opcode_hash = htab_create_alloc (16, hash_string_tuple, eq_string_tuple,
                                       arc_opcode_free, xcalloc, free);

  do
    {
      const char *name = opcode->name;
      arc_insert_opcode (opcode);

      while (++opcode && opcode->name
             && (opcode->name == name
                 || !strcmp (opcode->name, name)))
        continue;
    } while (opcode->name);
}

void declare_core_registers(void)
{
  declare_register ("gp", 26);
  declare_register ("fp", 27);
  declare_register ("sp", 28);
  declare_register ("ilink", 29);
  declare_register ("ilink1", 29);
  declare_register ("ilink2", 30);
  declare_register ("blink", 31);
}

void declare_xy_memory_register(const char *prefix, int x_index, const char *suffix, int base_reg)
{
  char reg_name[16];
  sprintf(reg_name, "%s%d%s", prefix, x_index, suffix);
  declare_register (reg_name, base_reg);
}

void declare_xy_memory_registers(void)
{
  #define XY_REG_BASE_U0 32
  #define XY_REG_BASE_NU 48
  #define XY_REG_COUNT 4
  
  int i;
  for (i = 0; i < XY_REG_COUNT; i++)
    {
      declare_xy_memory_register("x", i, "_u0", XY_REG_BASE_U0 + i * 2);
      declare_xy_memory_register("x", i, "_u1", XY_REG_BASE_U0 + i * 2 + 1);
    }
  
  for (i = 0; i < XY_REG_COUNT; i++)
    {
      declare_xy_memory_register("y", i, "_u0", XY_REG_BASE_U0 + 8 + i * 2);
      declare_xy_memory_register("y", i, "_u1", XY_REG_BASE_U0 + 8 + i * 2 + 1);
    }
  
  for (i = 0; i < XY_REG_COUNT; i++)
    {
      declare_xy_memory_register("x", i, "_nu", XY_REG_BASE_NU + i);
      declare_xy_memory_register("y", i, "_nu", XY_REG_BASE_NU + XY_REG_COUNT + i);
    }
}

void declare_special_registers(void)
{
  declare_register ("mlo", 57);
  declare_register ("mmid", 58);
  declare_register ("mhi", 59);
  declare_register ("acc1", 56);
  declare_register ("acc2", 57);
  declare_register ("lp_count", 60);
  declare_register ("pcl", 63);
}

void initialize_registers(void)
{
  arc_reg_hash = str_htab_create ();
  declare_register_set ();
  declare_core_registers();
  declare_xy_memory_registers();
  declare_special_registers();
}

void initialize_aux_registers(void)
{
  const struct arc_aux_reg *auxr = &arc_aux_regs[0];
  unsigned int i;
  
  arc_aux_hash = str_htab_create ();
  
  for (i = 0; i < arc_num_aux_regs; i++, auxr++)
    {
      if (!(auxr->cpu & selected_cpu.flags))
        continue;

      if ((auxr->subclass != NONE) && !check_cpu_feature (auxr->subclass))
        continue;

      if (str_hash_insert (arc_aux_hash, auxr->name, auxr, 0) != 0)
        as_fatal (_("duplicate %s"), auxr->name);
    }
}

void initialize_address_types(void)
{
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

void md_begin (void)
{
  initialize_cpu_and_architecture();
  initialize_opcode_hash_table();
  initialize_registers();
  memset (&arc_last_insns[0], 0, sizeof (arc_last_insns));
  initialize_aux_registers();
  initialize_address_types();
}

void
arc_md_end (void)
{
  htab_delete (arc_opcode_hash);
  htab_delete (arc_reg_hash);
  htab_delete (arc_aux_hash);
  htab_delete (arc_addrtype_hash);
}

/* Write a value out to the object file, using the appropriate
   endianness.  */

void md_number_to_chars(char *buf, valueT val, int n)
{
    void (*conversion_function)(char *, valueT, int) = 
        target_big_endian ? number_to_chars_bigendian : number_to_chars_littleendian;
    
    conversion_function(buf, val, n);
}

/* Round up a section size to the appropriate boundary.  */

valueT
md_section_align (segT segment,
		  valueT size)
{
  int align = bfd_section_alignment (segment);
  valueT alignment_mask = (valueT) 1 << align;
  valueT alignment_offset = alignment_mask - 1;

  return ((size + alignment_offset) & (-alignment_mask));
}

/* The location from which a PC relative jump should be calculated,
   given a PC relative reloc.  */

#define ALIGNMENT_MASK (~3)
#define LIMM_COMPENSATION 4

static int is_symbol_undefined_or_different_segment(fixS *fixP, segT sec)
{
    return fixP->fx_addsy != NULL
           && (!S_IS_DEFINED(fixP->fx_addsy)
               || S_GET_SEGMENT(fixP->fx_addsy) != sec);
}

static int is_pcrel_relocation_type(int reloc_type)
{
    switch (reloc_type)
    {
    case BFD_RELOC_ARC_PC32:
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
        return 1;
    default:
        return 0;
    }
}

static offsetT adjust_base_for_relocation(offsetT base, fixS *fixP)
{
    if ((int)fixP->fx_r_type < 0)
    {
        return base & ALIGNMENT_MASK;
    }
    
    if (fixP->fx_r_type == BFD_RELOC_ARC_PC32)
    {
        base -= LIMM_COMPENSATION;
    }
    
    if (is_pcrel_relocation_type(fixP->fx_r_type))
    {
        return base & ALIGNMENT_MASK;
    }
    
    as_bad_where(fixP->fx_file, fixP->fx_line,
                 _("unhandled reloc %s in md_pcrel_from_section"),
                 bfd_get_reloc_code_name(fixP->fx_r_type));
    return base;
}

static void debug_print_pcrel_info(fixS *fixP, offsetT base)
{
    pr_debug("pcrel from %" PRIx64 " + %lx = %" PRIx64 ", "
             "symbol: %s (%" PRIx64 ")\n",
             (uint64_t)fixP->fx_frag->fr_address, fixP->fx_where, (uint64_t)base,
             fixP->fx_addsy ? S_GET_NAME(fixP->fx_addsy) : "(null)",
             fixP->fx_addsy ? (uint64_t)S_GET_VALUE(fixP->fx_addsy) : (uint64_t)0);
}

long
md_pcrel_from_section(fixS *fixP, segT sec)
{
    offsetT base = fixP->fx_where + fixP->fx_frag->fr_address;
    
    pr_debug("pcrel_from_section, fx_offset = %d\n", (int)fixP->fx_offset);
    
    if (is_symbol_undefined_or_different_segment(fixP, sec))
    {
        pr_debug("Unknown pcrel symbol: %s\n", S_GET_NAME(fixP->fx_addsy));
        return 0;
    }
    
    base = adjust_base_for_relocation(base, fixP);
    
    debug_print_pcrel_info(fixP, base);
    
    return base;
}

/* Given a BFD relocation find the corresponding operand.  */

static const struct arc_operand *
find_operand_for_reloc (extended_bfd_reloc_code_real_type reloc)
{
  unsigned i;

  for (i = 0; i < arc_num_operands; i++)
    if (arc_operands[i].default_reloc == reloc)
      return &arc_operands[i];
  return NULL;
}

/* Insert an operand value into an instruction.  */

static void calculate_operand_range(const struct arc_operand *operand, offsetT *min, offsetT *max)
{
  if (operand->flags & ARC_OPERAND_SIGNED)
    {
      *max = (1 << (operand->bits - 1)) - 1;
      *min = -(1 << (operand->bits - 1));
    }
  else
    {
      *max = (1 << operand->bits) - 1;
      *min = 0;
    }
}

static int should_validate_range(const struct arc_operand *operand)
{
  return operand->bits != 32
         && !(operand->flags & ARC_OPERAND_NCHK)
         && !(operand->flags & ARC_OPERAND_FAKE);
}

static void validate_operand_range(const struct arc_operand *operand,
                                  long long val,
                                  const char *file,
                                  unsigned line)
{
  offsetT min = 0, max = 0;
  
  if (!should_validate_range(operand))
    return;
    
  calculate_operand_range(operand, &min, &max);
  
  if (val < min || val > max)
    as_bad_value_out_of_range(_("operand"), val, min, max, file, line);
    
  pr_debug("insert field: %ld <= %lld <= %ld\n", min, val, max);
}

#define ALIGNMENT_32BIT 0x03
#define ALIGNMENT_16BIT 0x01
#define SHIFT_32BIT_ALIGNED 2
#define SHIFT_16BIT_ALIGNED 1

static void check_alignment(const struct arc_operand *operand,
                           long long val,
                           const char *file,
                           unsigned line)
{
  if ((operand->flags & ARC_OPERAND_ALIGNED32) && (val & ALIGNMENT_32BIT))
    as_bad_where(file, line, _("Unaligned operand. Needs to be 32bit aligned"));
    
  if ((operand->flags & ARC_OPERAND_ALIGNED16) && (val & ALIGNMENT_16BIT))
    as_bad_where(file, line, _("Unaligned operand. Needs to be 16bit aligned"));
}

static unsigned long long insert_with_custom_function(unsigned long long insn,
                                                     const struct arc_operand *operand,
                                                     long long val,
                                                     const char *file,
                                                     unsigned line)
{
  const char *errmsg = NULL;
  insn = (*operand->insert)(insn, val, &errmsg);
  if (errmsg)
    as_warn_where(file, line, "%s", errmsg);
  return insn;
}

static long long apply_truncation(const struct arc_operand *operand, long long val)
{
  if (!(operand->flags & ARC_OPERAND_TRUNCATE))
    return val;
    
  if (operand->flags & ARC_OPERAND_ALIGNED32)
    val >>= SHIFT_32BIT_ALIGNED;
  if (operand->flags & ARC_OPERAND_ALIGNED16)
    val >>= SHIFT_16BIT_ALIGNED;
    
  return val;
}

static unsigned long long insert_standard(unsigned long long insn,
                                         const struct arc_operand *operand,
                                         long long val)
{
  val = apply_truncation(operand, val);
  insn |= ((val & ((1 << operand->bits) - 1)) << operand->shift);
  return insn;
}

static unsigned long long
insert_operand(unsigned long long insn,
               const struct arc_operand *operand,
               long long val,
               const char *file,
               unsigned line)
{
  validate_operand_range(operand, val, file, line);
  check_alignment(operand, val, file, line);
  
  if (operand->insert)
    return insert_with_custom_function(insn, operand, val, file, line);
  
  return insert_standard(insn, operand, val);
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
    add_symbol_segment = S_GET_SEGMENT (fx_addsy);

  if (!process_subtraction_symbol(fixP, &fx_subsy, &fx_offset, &sub_symbol_segment))
    return;

  process_addition_symbol(fixP, &fx_addsy, &fx_offset, &value, add_symbol_segment, seg);

  if (!fx_addsy)
    fixP->fx_done = true;

  handle_pcrel_fixup(fixP, &value, fx_addsy, seg);

  pr_debug ("%s:%u: apply_fix: r_type=%d (%s) value=0x%lX offset=0x%lX\n",
	    fixP->fx_file, fixP->fx_line, fixP->fx_r_type,
	    ((int) fixP->fx_r_type < 0) ? "Internal":
	    bfd_get_reloc_code_name (fixP->fx_r_type), value,
	    fixP->fx_offset);

  reloc = fixP->fx_r_type;
  handle_tls_relocations(fixP, reloc);

  if (!fixP->fx_done)
    return;

  value += fx_offset;

  if (value & 0x80000000)
    value |= (-1UL << 31);

  reloc = fixP->fx_r_type;
  
  if (handle_simple_relocations(fixP, fixpos, value, reloc))
    return;

  operand = get_operand_for_reloc(fixP, reloc);
  if (!operand)
    return;

  insn = read_instruction(fixpos, fixP->fx_size, fixP->fx_file, fixP->fx_line);
  insn = insert_operand (insn, operand, (offsetT) value,
			 fixP->fx_file, fixP->fx_line);
  md_number_to_chars_midend (fixpos, insn, fixP->fx_size);
}

static bool
process_subtraction_symbol(fixS *fixP, symbolS **fx_subsy, offsetT *fx_offset, segT *sub_symbol_segment)
{
  if (!*fx_subsy || is_tls_reloc_with_subtraction(fixP->fx_r_type))
    return true;

  resolve_symbol_value (*fx_subsy);
  *sub_symbol_segment = S_GET_SEGMENT (*fx_subsy);

  if (*sub_symbol_segment == absolute_section)
    {
      *fx_offset -= S_GET_VALUE (*fx_subsy);
      *fx_subsy = NULL;
    }
  else
    {
      as_bad_subtract (fixP);
      return false;
    }
  return true;
}

static bool
is_tls_reloc_with_subtraction(extended_bfd_reloc_code_real_type r_type)
{
  return r_type == BFD_RELOC_ARC_TLS_DTPOFF ||
         r_type == BFD_RELOC_ARC_TLS_DTPOFF_S9 ||
         r_type == BFD_RELOC_ARC_TLS_GD_LD;
}

static void
process_addition_symbol(fixS *fixP, symbolS **fx_addsy, offsetT *fx_offset, valueT *value, segT add_symbol_segment, segT seg)
{
  if (!*fx_addsy || S_IS_WEAK (*fx_addsy))
    return;

  if (add_symbol_segment == seg && fixP->fx_pcrel)
    {
      *value += S_GET_VALUE (*fx_addsy);
      *value -= md_pcrel_from_section (fixP, seg);
      *fx_addsy = NULL;
      fixP->fx_pcrel = false;
    }
  else if (add_symbol_segment == absolute_section)
    {
      *value = fixP->fx_offset;
      *fx_offset += S_GET_VALUE (fixP->fx_addsy);
      *fx_addsy = NULL;
      fixP->fx_pcrel = false;
    }
}

static void
handle_pcrel_fixup(fixS *fixP, valueT *value, symbolS *fx_addsy, segT seg)
{
  if (!fixP->fx_pcrel)
    return;

  if (should_adjust_pcrel_value(fx_addsy, seg))
    *value += md_pcrel_from_section (fixP, seg);

  adjust_pcrel_reloc_type(fixP);
}

static bool
should_adjust_pcrel_value(symbolS *fx_addsy, segT seg)
{
  return fx_addsy &&
         ((S_IS_DEFINED (fx_addsy) && S_GET_SEGMENT (fx_addsy) != seg) ||
          S_IS_WEAK (fx_addsy));
}

static void
adjust_pcrel_reloc_type(fixS *fixP)
{
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
                      _("PC relative relocation not allowed for (internal)"
                        " type %d"),
                      fixP->fx_r_type);
      break;
    }
}

static void
handle_tls_relocations(fixS *fixP, extended_bfd_reloc_code_real_type reloc)
{
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
          fixP->fx_offset = (S_GET_VALUE (fixP->fx_subsy) -
                            fixP->fx_frag->fr_address - fixP->fx_where);
          fixP->fx_subsy = NULL;
        }
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

static bool
handle_simple_relocations(fixS *fixP, char *fixpos, valueT value, extended_bfd_reloc_code_real_type reloc)
{
  switch (reloc)
    {
    case BFD_RELOC_8:
    case BFD_RELOC_16:
    case BFD_RELOC_24:
    case BFD_RELOC_32:
    case BFD_RELOC_64:
    case BFD_RELOC_ARC_32_PCREL:
      md_number_to_chars (fixpos, value, fixP->fx_size);
      return true;

    case BFD_RELOC_ARC_GOTPC32:
      as_bad (_("Unsupported operation on reloc"));
      return true;

    case BFD_RELOC_ARC_TLS_DTPOFF:
    case BFD_RELOC_ARC_TLS_LE_32:
      gas_assert (!fixP->fx_addsy);
      gas_assert (!fixP->fx_subsy);
    case BFD_RELOC_ARC_GOTOFF:
    case BFD_RELOC_ARC_32_ME:
    case BFD_RELOC_ARC_PC32:
    case BFD_RELOC_ARC_PLT32:
      md_number_to_chars_midend (fixpos, value, fixP->fx_size);
      return true;

    default:
      return false;
    }
}

static const struct arc_operand *
get_operand_for_reloc(fixS *fixP, extended_bfd_reloc_code_real_type reloc)
{
  const struct arc_operand *operand = NULL;

  switch (reloc)
    {
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
    default:
      break;
    }

  switch (reloc)
    {
    case BFD_RELOC_ARC_S25W_PCREL:
    case BFD_RELOC_ARC_S21W_PCREL:
    case BFD_RELOC_ARC_S21H_PCREL:
    case BFD_RELOC_ARC_S25H_PCREL:
    case BFD_RELOC_ARC_S13_PCREL:
      operand = find_operand_for_reloc (reloc);
      gas_assert (operand);
      break;

    default:
      if ((int) fixP->fx_r_type >= 0)
        as_fatal (_("unhandled relocation type %s"),
                  bfd_get_reloc_code_name (fixP->fx_r_type));

      if (fixP->fx_addsy != 0 &&
          S_GET_SEGMENT (fixP->fx_addsy) != absolute_section)
        as_bad_where (fixP->fx_file, fixP->fx_line,
                      _("non-absolute expression in constant field"));

      gas_assert (-(int) fixP->fx_r_type < (int) arc_num_operands);
      operand = &arc_operands[-(int) fixP->fx_r_type];
      break;
    }

  return operand;
}

static unsigned
read_instruction(char *fixpos, int size, const char *file, unsigned int line)
{
  unsigned insn = 0;

  if (target_big_endian)
    {
      switch (size)
        {
        case 4:
          insn = bfd_getb32 (fixpos);
          break;
        case 2:
          insn = bfd_getb16 (fixpos);
          break;
        default:
          as_bad_where (file, line, _("unknown fixup size"));
        }
    }
  else
    {
      switch (size)
        {
        case 4:
          insn = bfd_getl16 (fixpos) << 16 | bfd_getl16 (fixpos + 2);
          break;
        case 2:
          insn = bfd_getl16 (fixpos);
          break;
        default:
          as_bad_where (file, line, _("unknown fixup size"));
        }
    }

  return insn;
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
md_estimate_size_before_relax (fragS *fragP, segT segment)
{
  if (should_use_maximum_size(fragP, segment))
    {
      advance_to_maximum_subtype(fragP);
    }

  int growth = md_relax_table[fragP->fr_subtype].rlx_length;
  fragP->fr_var = growth;

  pr_debug ("%s:%d: md_estimate_size_before_relax: %d\n",
           fragP->fr_file, fragP->fr_line, growth);

  return growth;
}

static int
should_use_maximum_size (fragS *fragP, segT segment)
{
  return is_different_non_absolute_segment(fragP, segment) ||
         is_constant_non_pcrel(fragP) ||
         symbol_equated_p(fragP->fr_symbol) ||
         S_IS_WEAK(fragP->fr_symbol);
}

static int
is_different_non_absolute_segment (fragS *fragP, segT segment)
{
  segT symbol_segment = S_GET_SEGMENT(fragP->fr_symbol);
  return symbol_segment != segment && symbol_segment != absolute_section;
}

static int
is_constant_non_pcrel (fragS *fragP)
{
  return symbol_constant_p(fragP->fr_symbol) && !fragP->tc_frag_data.pcrel;
}

static void
advance_to_maximum_subtype (fragS *fragP)
{
  while (md_relax_table[fragP->fr_subtype].rlx_more != ARC_RLX_NONE)
    {
      ++fragP->fr_subtype;
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

  if (!fixP->fx_pcrel != !reloc->howto->pc_relative)
    as_fatal (_("internal error? cannot generate `%s' relocation"),
	      bfd_get_reloc_code_name (code));

  gas_assert (!fixP->fx_pcrel == !reloc->howto->pc_relative);

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

  if (fragP->fr_subtype <= 0
      && fragP->fr_subtype >= arc_num_relax_opcodes)
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
  if (!is_global_offset_table_name(name))
    return NULL;

  return get_or_create_got_symbol(name);
}

static int
is_global_offset_table_name(const char *name)
{
  return ((*name == '_')
          && (*(name+1) == 'G')
          && (strcmp(name, GLOBAL_OFFSET_TABLE_NAME) == 0));
}

static symbolS *
get_or_create_got_symbol(const char *name)
{
  if (!GOT_symbol)
    create_got_symbol(name);
  
  return GOT_symbol;
}

static void
create_got_symbol(const char *name)
{
  if (symbol_find(name))
    as_bad("GOT already in symbol table");

  GOT_symbol = symbol_new(GLOBAL_OFFSET_TABLE_NAME, undefined_section,
                         &zero_address_frag, 0);
}

/* Turn a string in input_line_pointer into a floating point constant
   of type type, and store the appropriate bytes in *litP.  The number
   of LITTLENUMS emitted is stored in *sizeP.  An error message is
   returned, or NULL on OK.  */

const char *
md_atof (int type, char *litP, int *sizeP)
{
  return ieee_md_atof (type, litP, sizeP, target_big_endian);
}

/* Called for any expression that can not be recognized.  When the
   function is called, `input_line_pointer' will point to the start of
   the expression.  We use it when we have complex operations like
   @label1 - @label2.  */

void md_operand(expressionS *expressionP)
{
    if (*input_line_pointer != '@') {
        return;
    }
    
    input_line_pointer++;
    expressionP->X_op = O_symbol;
    expressionP->X_md = O_absent;
    expression(expressionP);
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

  sym = str_hash_find (arc_reg_hash, name);
  if (sym)
    {
      e->X_op = O_register;
      e->X_add_number = S_GET_VALUE (sym);
      return true;
    }

  sym = str_hash_find (arc_addrtype_hash, name);
  if (sym)
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

static void print_cpu_name(FILE *stream, const char *name, bool is_last)
{
    fprintf(stream, "%s%s", name, is_last ? "\n" : ", ");
}

static int get_name_display_length(const char *name, bool is_last)
{
    return strlen(name) + (is_last ? 0 : 2);
}

static bool should_wrap_line(int current_offset, int additional_length)
{
    #define MAX_LINE_WIDTH 80
    return current_offset + additional_length > MAX_LINE_WIDTH;
}

static int print_indentation(FILE *stream)
{
    static const char *space_buf = "                          ";
    fprintf(stream, "%s", space_buf);
    return strlen(space_buf);
}

static void start_new_line(FILE *stream, int *offset)
{
    fprintf(stream, "\n");
    *offset = print_indentation(stream);
}

static void arc_show_cpu_list(FILE *stream)
{
    int offset = print_indentation(stream);
    
    for (int i = 0; cpu_types[i].name != NULL; ++i)
    {
        bool is_last = (cpu_types[i + 1].name == NULL);
        int display_length = get_name_display_length(cpu_types[i].name, is_last);
        
        if (should_wrap_line(offset, display_length))
        {
            start_new_line(stream, &offset);
        }
        
        print_cpu_name(stream, cpu_types[i].name, is_last);
        offset += display_length;
    }
}

void
md_show_usage (FILE *stream)
{
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

static bool name_matches(const struct arc_reloc_equiv_tab *r, const char *name)
{
    return strcmp(name, r->name) == 0;
}

static bool mnemonic_matches(const struct arc_reloc_equiv_tab *r, const char *opcodename)
{
    return !r->mnemonic || strcmp(r->mnemonic, opcodename) == 0;
}

static bool flag_exists_in_list(const struct arc_flags *pflags, int nflg, unsigned flag_index)
{
    int j;
    for (j = 0; j < nflg; j++)
    {
        if (!strcmp(pflags[j].name, arc_flag_operands[flag_index].name))
            return true;
    }
    return false;
}

static bool all_flags_match(const struct arc_reloc_equiv_tab *r, const struct arc_flags *pflags, int nflg)
{
    const unsigned *psflg;
    
    if (!r->flags[0])
        return true;
        
    if (!nflg)
        return false;
    
    psflg = r->flags;
    while (*psflg)
    {
        if (!flag_exists_in_list(pflags, nflg, *psflg))
            return false;
        psflg++;
    }
    
    return true;
}

static bool reloc_matches(const struct arc_reloc_equiv_tab *r, extended_bfd_reloc_code_real_type reloc)
{
    return reloc == r->oldreloc;
}

static bool entry_matches(const struct arc_reloc_equiv_tab *r,
                          const char *name,
                          const char *opcodename,
                          const struct arc_flags *pflags,
                          int nflg,
                          extended_bfd_reloc_code_real_type reloc)
{
    return name_matches(r, name) &&
           mnemonic_matches(r, opcodename) &&
           all_flags_match(r, pflags, nflg) &&
           reloc_matches(r, reloc);
}

static extended_bfd_reloc_code_real_type
find_reloc(const char *name,
           const char *opcodename,
           const struct arc_flags *pflags,
           int nflg,
           extended_bfd_reloc_code_real_type reloc)
{
    unsigned int i;
    
    for (i = 0; i < arc_num_equiv_tab; i++)
    {
        const struct arc_reloc_equiv_tab *r = &arc_reloc_equiv[i];
        
        if (entry_matches(r, name, opcodename, pflags, nflg, reloc))
            return r->newreloc;
    }
    
    as_bad(_("Unable to find %s relocation for instruction %s"),
           name, opcodename);
    return BFD_RELOC_UNUSED;
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

static bool check_flag_match(const struct arc_flag_operand *flag_opand,
                             const struct arc_flags *pflags,
                             int nflgs)
{
    for (int i = 0; i < nflgs; ++i)
    {
        if (strcmp(flag_opand->name, pflags[i].name) == 0)
            return true;
    }
    return false;
}

static int count_matching_flags_in_class(unsigned flag_class,
                                         const struct arc_flags *pflags,
                                         int nflgs)
{
    int count = 0;
    unsigned flag_idx = 0;
    unsigned flag;
    
    while ((flag = arc_flag_classes[flag_class].flags[flag_idx]) != 0)
    {
        const struct arc_flag_operand *flag_opand = &arc_flag_operands[flag];
        if (check_flag_match(flag_opand, pflags, nflgs))
            ++count;
        ++flag_idx;
    }
    
    return count;
}

static bool
relaxable_flag (const struct arc_relaxable_ins *ins,
		const struct arc_flags *pflags,
		int nflgs)
{
    unsigned flag_class_idx = 0;
    unsigned flag_class;
    int counttrue = 0;

    while ((flag_class = ins->flag_classes[flag_class_idx]) != 0)
    {
        counttrue += count_matching_flags_in_class(flag_class, pflags, nflgs);
        ++flag_class_idx;
    }

    return counttrue == nflgs;
}

/* Checks if operands are in line with relaxable insn.  */

static bool is_arithmetic_operator(O_operator op)
{
    return op == O_multiply || op == O_divide || op == O_modulus || 
           op == O_add || op == O_subtract || op == O_symbol;
}

static bool is_valid_register_s(int reg_num)
{
    return (reg_num >= 0 && reg_num <= 3) || 
           (reg_num >= 12 && reg_num <= 15);
}

static bool check_immediate(const expressionS *epr)
{
    return is_arithmetic_operator(epr->X_op);
}

static bool check_register_dup(const expressionS *epr, const expressionS *prev)
{
    return prev != NULL && epr->X_add_number == prev->X_add_number;
}

static bool check_register(const expressionS *epr)
{
    return epr->X_op == O_register;
}

static bool check_register_s(const expressionS *epr)
{
    return epr->X_op == O_register && is_valid_register_s(epr->X_add_number);
}

#define GP_REGISTER 26

static bool check_register_no_gp(const expressionS *epr)
{
    return epr->X_op == O_register && epr->X_add_number != GP_REGISTER;
}

static bool check_bracket(const expressionS *epr)
{
    return epr->X_op == O_bracket;
}

static bool validate_operand(enum rlx_operand_type operand, 
                            const expressionS *epr, 
                            const expressionS *prev)
{
    switch (operand)
    {
    case IMMEDIATE:
        return check_immediate(epr);
    case REGISTER_DUP:
        return check_register_dup(epr, prev) && check_register(epr);
    case REGISTER:
        return check_register(epr);
    case REGISTER_S:
        return check_register_s(epr);
    case REGISTER_NO_GP:
        return check_register_no_gp(epr);
    case BRACKET:
        return check_bracket(epr);
    default:
        return false;
    }
}

static bool
relaxable_operand (const struct arc_relaxable_ins *ins,
		   const expressionS *tok,
		   int ntok)
{
    const enum rlx_operand_type *operand = &ins->operands[0];
    int i = 0;

    while (*operand != EMPTY)
    {
        if (i != 0 && i >= ntok)
            return false;

        const expressionS *epr = &tok[i];
        const expressionS *prev = (i > 0) ? &tok[i - 1] : NULL;

        if (!validate_operand(*operand, epr, prev))
            return false;

        ++i;
        operand = &ins->operands[i];
    }

    return i == ntok;
}

/* Return TRUE if this OPDCODE is a candidate for relaxation.  */

static bool is_relaxable_instruction(const struct arc_opcode *opcode,
                                     const struct arc_relaxable_ins *arc_rlx_ins,
                                     const expressionS *tok,
                                     int ntok,
                                     const struct arc_flags *pflags,
                                     int nflg)
{
    return (strcmp(opcode->name, arc_rlx_ins->mnemonic_r) == 0)
           && may_relax_expr(tok[arc_rlx_ins->opcheckidx])
           && relaxable_operand(arc_rlx_ins, tok, ntok)
           && relaxable_flag(arc_rlx_ins, pflags, nflg);
}

static void setup_fragment_data(const expressionS *tok,
                               int ntok,
                               const struct arc_flags *pflags,
                               int nflg,
                               int subtype)
{
    frag_now->fr_subtype = subtype;
    memcpy(&frag_now->tc_frag_data.tok, tok, sizeof(expressionS) * ntok);
    memcpy(&frag_now->tc_frag_data.pflags, pflags, sizeof(struct arc_flags) * nflg);
    frag_now->tc_frag_data.nflg = nflg;
    frag_now->tc_frag_data.ntok = ntok;
}

static bool relax_insn_p(const struct arc_opcode *opcode,
                         const expressionS *tok,
                         int ntok,
                         const struct arc_flags *pflags,
                         int nflg)
{
    if (!relaxation_state)
        return false;

    for (unsigned i = 0; i < arc_num_relaxable_ins; ++i)
    {
        const struct arc_relaxable_ins *arc_rlx_ins = &arc_relaxable_insns[i];

        if (is_relaxable_instruction(opcode, arc_rlx_ins, tok, ntok, pflags, nflg))
        {
            setup_fragment_data(tok, ntok, pflags, nflg, arc_relaxable_insns[i].subtype);
            return true;
        }
    }

    return false;
}

/* Turn an opcode description and a set of arguments into
   an instruction and a fixup.  */

static void process_register_operand(unsigned long long *image, 
                                     const struct arc_operand *operand,
                                     const expressionS *t)
{
    *image = insert_operand(*image, operand, regno(t->X_add_number), NULL, 0);
}

static void process_constant_operand(unsigned long long *image,
                                    const struct arc_operand *operand,
                                    const expressionS *t,
                                    struct arc_insn *insn,
                                    const expressionS **reloc_exp)
{
    *image = insert_operand(*image, operand, t->X_add_number, NULL, 0);
    *reloc_exp = t;
    if (operand->flags & ARC_OPERAND_LIMM)
        insn->limm = t->X_add_number;
}

static void process_register_range(unsigned long long *image,
                                  const struct arc_operand *operand,
                                  const expressionS *t)
{
    int regs = get_register(t->X_add_symbol) << 16;
    regs |= get_register(t->X_op_symbol);
    *image = insert_operand(*image, operand, regs, NULL, 0);
}

static extended_bfd_reloc_code_real_type handle_plt_relocation(const struct arc_opcode *opcode,
                                                               const struct arc_flags *pflags,
                                                               int nflg,
                                                               const struct arc_operand *operand)
{
    if (opcode->insn_class == JUMP)
        as_bad(_("Unable to use @plt relocation for insn %s"), opcode->name);
    return find_reloc("plt", opcode->name, pflags, nflg, operand->default_reloc);
}

static extended_bfd_reloc_code_real_type handle_pcl_relocation(const struct arc_opcode *opcode,
                                                               const struct arc_operand *operand,
                                                               const expressionS *t)
{
    if (operand->flags & ARC_OPERAND_LIMM)
    {
        if (arc_opcode_len(opcode) == 2 || opcode->insn_class == JUMP)
            as_bad(_("Unable to use @pcl relocation for insn %s"), opcode->name);
        return ARC_RELOC_TABLE(t->X_md)->reloc;
    }
    return operand->default_reloc;
}

static extended_bfd_reloc_code_real_type determine_relocation(const expressionS *t,
                                                             const struct arc_opcode *opcode,
                                                             const struct arc_flags *pflags,
                                                             int nflg,
                                                             const struct arc_operand *operand,
                                                             bool *needGOTSymbol)
{
    *needGOTSymbol = false;
    
    switch (t->X_md)
    {
    case O_plt:
        *needGOTSymbol = true;
        return handle_plt_relocation(opcode, pflags, nflg, operand);
        
    case O_gotoff:
    case O_gotpc:
        *needGOTSymbol = true;
        return ARC_RELOC_TABLE(t->X_md)->reloc;
        
    case O_pcl:
        return handle_pcl_relocation(opcode, operand, t);
        
    case O_sda:
        return find_reloc("sda", opcode->name, pflags, nflg, operand->default_reloc);
        
    case O_tlsgd:
    case O_tlsie:
        *needGOTSymbol = true;
    case O_tpoff:
    case O_dtpoff:
        return ARC_RELOC_TABLE(t->X_md)->reloc;
        
    case O_tpoff9:
    case O_dtpoff9:
        as_bad(_("TLS_*_S9 relocs are not supported yet"));
        break;
        
    default:
        return operand->default_reloc;
    }
    
    return operand->default_reloc;
}

static void add_fixup(struct arc_insn *insn,
                     const expressionS *t,
                     extended_bfd_reloc_code_real_type reloc,
                     const struct arc_operand *operand)
{
    if (insn->nfixups >= MAX_INSN_FIXUPS)
        as_fatal(_("too many fixups"));
        
    struct arc_fixup *fixup = &insn->fixups[insn->nfixups++];
    fixup->exp = *t;
    fixup->reloc = reloc;
    
    unsigned char pcrel;
    if ((int)reloc < 0)
    {
        pcrel = (operand->flags & ARC_OPERAND_PCREL) ? 1 : 0;
    }
    else
    {
        reloc_howto_type *reloc_howto = bfd_reloc_type_lookup(stdoutput, fixup->reloc);
        pcrel = reloc_howto->pc_relative;
    }
    
    fixup->pcrel = pcrel;
    fixup->islong = (operand->flags & ARC_OPERAND_LIMM) != 0;
}

static void process_relocation_operand(unsigned long long *image,
                                      const expressionS *t,
                                      const struct arc_opcode *opcode,
                                      const struct arc_flags *pflags,
                                      int nflg,
                                      const struct arc_operand *operand,
                                      struct arc_insn *insn,
                                      const expressionS **reloc_exp)
{
    bool needGOTSymbol;
    extended_bfd_reloc_code_real_type reloc = determine_relocation(t, opcode, pflags, 
                                                                   nflg, operand, &needGOTSymbol);
    
    if (needGOTSymbol && (GOT_symbol == NULL))
        GOT_symbol = symbol_find_or_make(GLOBAL_OFFSET_TABLE_NAME);
        
    *reloc_exp = t;
    add_fixup(insn, t, reloc, operand);
}

static void process_operand(unsigned long long *image,
                           const expressionS *t,
                           const struct arc_opcode *opcode,
                           const struct arc_flags *pflags,
                           int nflg,
                           const struct arc_operand *operand,
                           struct arc_insn *insn,
                           const expressionS **reloc_exp)
{
    switch (t->X_op)
    {
    case O_register:
        process_register_operand(image, operand, t);
        break;
        
    case O_constant:
        process_constant_operand(image, operand, t, insn, reloc_exp);
        break;
        
    case O_bracket:
    case O_colon:
    case O_addrtype:
        break;
        
    case O_absent:
        gas_assert(operand->flags & ARC_OPERAND_IGNORE);
        break;
        
    case O_subtract:
        if ((t->X_add_number == 0) && contains_register(t->X_add_symbol) && 
            contains_register(t->X_op_symbol))
        {
            process_register_range(image, operand, t);
            break;
        }
        
    default:
        process_relocation_operand(image, t, opcode, pflags, nflg, operand, insn, reloc_exp);
        break;
    }
}

static unsigned get_bit_y_operand(const char *flag_name, const char *opcode_name)
{
    bool is_t_flag = !strcmp(flag_name, "t");
    bool is_bbit = !strcmp(opcode_name, "bbit0") || !strcmp(opcode_name, "bbit1");
    
    if (is_t_flag)
        return is_bbit ? arc_NToperand : arc_Toperand;
    else
        return is_bbit ? arc_Toperand : arc_NToperand;
}

static void process_conditional_flag(unsigned long long *image,
                                    const struct arc_flag_operand *flg_operand,
                                    const struct arc_opcode *opcode,
                                    const expressionS *reloc_exp,
                                    struct arc_insn *insn,
                                    unsigned char pcrel)
{
    unsigned bitYoperand = get_bit_y_operand(flg_operand->name, opcode->name);
    
    gas_assert(reloc_exp != NULL);
    
    if (reloc_exp->X_op == O_constant)
    {
        offsetT val = reloc_exp->X_add_number;
        *image |= insert_operand(*image, &arc_operands[bitYoperand], val, NULL, 0);
    }
    else
    {
        if (insn->nfixups >= MAX_INSN_FIXUPS)
            as_fatal(_("too many fixups"));
            
        struct arc_fixup *fixup = &insn->fixups[insn->nfixups++];
        fixup->exp = *reloc_exp;
        fixup->reloc = -bitYoperand;
        fixup->pcrel = pcrel;
        fixup->islong = false;
    }
}

static void process_flag(unsigned long long *image,
                       const struct arc_flag_operand *flg_operand,
                       const struct arc_opcode *opcode,
                       const expressionS *reloc_exp,
                       struct arc_insn *insn,
                       unsigned char pcrel,
                       bool *has_delay_slot)
{
    if (!strcmp(flg_operand->name, "d"))
        *has_delay_slot = true;
        
    if ((selected_cpu.flags & ARC_OPCODE_ARCV2) &&
        (!strcmp(flg_operand->name, "t") || !strcmp(flg_operand->name, "nt")))
    {
        process_conditional_flag(image, flg_operand, opcode, reloc_exp, insn, pcrel);
    }
    else
    {
        *image |= (flg_operand->code & ((1 << flg_operand->bits) - 1)) << flg_operand->shift;
    }
}

static void update_last_insn_status(const struct arc_opcode *opcode,
                                   struct arc_insn *insn,
                                   bool has_delay_slot)
{
    arc_last_insns[1] = arc_last_insns[0];
    arc_last_insns[0].opcode = opcode;
    arc_last_insns[0].has_limm = insn->has_limm;
    arc_last_insns[0].has_delay_slot = has_delay_slot;
}

static void validate_instruction_sequence(void)
{
    if (arc_last_insns[1].has_delay_slot && 
        is_br_jmp_insn_p(arc_last_insns[0].opcode))
    {
        as_bad(_("Insn %s has a jump/branch instruction %s in its delay slot."),
               arc_last_insns[1].opcode->name,
               arc_last_insns[0].opcode->name);
    }
    
    if (arc_last_insns[1].has_delay_slot && arc_last_insns[0].has_limm)
    {
        as_bad(_("Insn %s has an instruction %s with limm in its delay slot."),
               arc_last_insns[1].opcode->name,
               arc_last_insns[0].opcode->name);
    }
}

static void assemble_insn(const struct arc_opcode *opcode,
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
    
    memset(insn, 0, sizeof(*insn));
    image = opcode->opcode;
    
    pr_debug("%s:%d: assemble_insn: %s using opcode %llx\n",
             frag_now->fr_file, frag_now->fr_line, opcode->name,
             opcode->opcode);
    
    for (argidx = opcode->operands; *argidx; ++argidx)
    {
        const struct arc_operand *operand = &arc_operands[*argidx];
        const expressionS *t = NULL;
        
        if (ARC_OPERAND_IS_FAKE(operand))
            continue;
            
        if (operand->flags & ARC_OPERAND_DUPLICATE)
        {
            tokidx++;
            continue;
        }
        
        if (tokidx >= ntok)
        {
            abort();
        }
        else
            t = &tok[tokidx++];
            
        if (operand->flags & ARC_OPERAND_LIMM)
            insn->has_limm = true;
            
        process_operand(&image, t, opcode, pflags, nflg, operand, insn, &reloc_exp);
    }
    
    for (i = 0; i < nflg; i++)
    {
        const struct arc_flag_operand *flg_operand = pflags[i].flgp;
        process_flag(&image, flg_operand, opcode, reloc_exp, insn, pcrel, &has_delay_slot);
    }
    
    insn->relax = relax_insn_p(opcode, tok, ntok, pflags, nflg);
    insn->len = arc_opcode_len(opcode);
    insn->insn = image;
    
    update_last_insn_status(opcode, insn, has_delay_slot);
    validate_instruction_sequence();
}

void arc_handle_align(fragS* fragP)
{
    if (fragP->fr_type != rs_align_code) {
        return;
    }
    
    char *dest = fragP->fr_literal + fragP->fr_fix;
    valueT count = fragP->fr_next->fr_address - fragP->fr_address - fragP->fr_fix;
    
    fragP->fr_var = 2;
    
    if (count & 1) {
        fragP->fr_fix++;
        *dest++ = 0;
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
      break;
    }

  return 1;
}

/* Compute the reloc type of an expression EXP.  */

static void
arc_check_reloc (expressionS *exp,
		 bfd_reloc_code_real_type *r_type_p)
{
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
  r_type = get_relocation_type_for_size(size, exp);
  fix_new_exp (frag, off, size, exp, 0, r_type);
}

static bfd_reloc_code_real_type
get_relocation_type_for_size(int size, expressionS *exp)
{
  #define SIZE_8_BIT  1
  #define SIZE_16_BIT 2
  #define SIZE_24_BIT 3
  #define SIZE_32_BIT 4
  #define SIZE_64_BIT 8

  if (size == SIZE_8_BIT)
    return BFD_RELOC_8;
  
  if (size == SIZE_16_BIT)
    return BFD_RELOC_16;
  
  if (size == SIZE_24_BIT)
    return BFD_RELOC_24;
  
  if (size == SIZE_32_BIT)
    return get_32bit_relocation(exp);
  
  if (size == SIZE_64_BIT)
    return BFD_RELOC_64;
  
  as_bad (_("unsupported BFD relocation size %u"), size);
  return BFD_RELOC_UNUSED;
}

static bfd_reloc_code_real_type
get_32bit_relocation(expressionS *exp)
{
  bfd_reloc_code_real_type r_type = BFD_RELOC_32;
  arc_check_reloc (exp, &r_type);
  return r_type;
}

/* The actual routine that checks the ZOL conditions.  */

static void check_arcv2_zol(symbolS *s)
{
    if (selected_cpu.flags & ARC_OPCODE_ARCv2EM)
        return;

    if (is_br_jmp_insn_p(arc_last_insns[0].opcode) || arc_last_insns[1].has_delay_slot)
        as_bad(_("Jump/Branch instruction detected at the end of the ZOL label @%s"),
               S_GET_NAME(s));
}

static void check_arc600_zol(symbolS *s)
{
    if (is_kernel_insn_p(arc_last_insns[0].opcode))
        as_bad(_("Kernel instruction detected at the end of the ZOL label @%s"),
               S_GET_NAME(s));

    if (arc_last_insns[0].has_limm && is_br_jmp_insn_p(arc_last_insns[0].opcode))
        as_bad(_("A jump instruction with long immediate detected at the \
end of the ZOL label @%s"), S_GET_NAME(s));
}

static void check_delay_slot_zol(symbolS *s)
{
    if (arc_last_insns[0].has_delay_slot)
        as_bad(_("An illegal use of delay slot detected at the end of the ZOL label @%s"),
               S_GET_NAME(s));
}

static void check_zol(symbolS *s)
{
    switch (selected_cpu.mach)
    {
    case bfd_mach_arc_arcv2:
        check_arcv2_zol(s);
        break;
    case bfd_mach_arc_arc600:
        check_arc600_zol(s);
        check_delay_slot_zol(s);
        break;
    case bfd_mach_arc_arc700:
        check_delay_slot_zol(s);
        break;
    default:
        break;
    }
}

/* If ZOL end check the last two instruction for illegals.  */
void
arc_frob_label (symbolS * sym)
{
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
  pr_debug ("arc_pcrel_adjust: address=%ld, fix=%ld, PCrel %s\n",
	    fragP->fr_address, fragP->fr_fix,
	    fragP->tc_frag_data.pcrel ? "Y" : "N");

  long adjusted_address = fragP->fr_address + fragP->fr_fix;

  if (!fragP->tc_frag_data.pcrel)
    return adjusted_address;

  #define PCL_ROUNDING_MASK 0x03
  return adjusted_address & PCL_ROUNDING_MASK;
}

/* Initialize the DWARF-2 unwind information for this procedure.  */

void
tc_arc_frame_initial_instructions (void)
{
  #define STACK_POINTER_REGISTER 28
  #define INITIAL_CFA_OFFSET 0
  
  cfi_add_CFA_def_cfa (STACK_POINTER_REGISTER, INITIAL_CFA_OFFSET);
}

int
tc_arc_regname_to_dw2regnum (char *regname)
{
  struct symbol *sym = str_hash_find (arc_reg_hash, regname);
  return sym ? S_GET_VALUE (sym) : -1;
}

/* Adjust the symbol table.  Delete found AUX register symbols.  */

void
arc_adjust_symtab (void)
{
  symbolS * sym;
  symbolS * next_sym;

  for (sym = symbol_rootP; sym != NULL; sym = next_sym)
    {
      next_sym = symbol_next (sym);
      
      if (ARC_GET_FLAG (sym) & ARC_FLAG_AUX)
	symbol_remove (sym, &symbol_rootP, &symbol_lastP);
    }

  elf_adjust_symtab ();
}

static char* get_instruction_name(void)
{
  char *p, c;
  char *insn_name;
  
  SKIP_WHITESPACE();
  p = input_line_pointer;
  c = get_symbol_name(&p);
  insn_name = xstrdup(p);
  restore_line_pointer(c);
  
  for (p = insn_name; *p; ++p)
    *p = TOLOWER(*p);
  
  return insn_name;
}

static int expect_comma_and_advance(const char *error_msg)
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

static unsigned char get_opcode_value(const char *comma_error_msg)
{
  if (!expect_comma_and_advance(comma_error_msg))
    return 0;
  return get_absolute_expression();
}

static int match_class_attribute(const void *class_array, size_t array_size, 
                                  size_t elem_size, unsigned char *result)
{
  unsigned int i;
  const struct { const char *name; size_t len; unsigned char attr_class; } *entry;
  
  for (i = 0; i < array_size; i++)
    {
      entry = (const void*)((char*)class_array + i * elem_size);
      if (!strncmp(entry->name, input_line_pointer, entry->len))
        {
          *result |= entry->attr_class;
          input_line_pointer += entry->len;
          return 1;
        }
    }
  return 0;
}

static unsigned char parse_class_with_pipe(const void *class_array, 
                                            size_t array_size, 
                                            size_t elem_size,
                                            const char *error_msg)
{
  unsigned char class_value = 0;
  
  while (1)
    {
      SKIP_WHITESPACE();
      
      if (!match_class_attribute(class_array, array_size, elem_size, &class_value))
        {
          as_bad(error_msg);
          ignore_rest_of_line();
          return 0;
        }
      
      SKIP_WHITESPACE();
      
      if (*input_line_pointer == '|')
        input_line_pointer++;
      else
        break;
    }
  
  return class_value;
}

static void parse_syntax_classes(unsigned char *syntax_class, 
                                  unsigned char *syntax_class_modifiers)
{
  while (1)
    {
      SKIP_WHITESPACE();
      
      if (!match_class_attribute(syntaxclassmod, ARRAY_SIZE(syntaxclassmod),
                                  sizeof(syntaxclassmod[0]), syntax_class_modifiers))
        {
          if (!match_class_attribute(syntaxclass, ARRAY_SIZE(syntaxclass),
                                      sizeof(syntaxclass[0]), syntax_class))
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
}

#define ARC_OP1_IMM_IMPLIED_FLAG 0x10

static void tokenize_extinsn(extInstruction_t *einsn)
{
  char *insn_name;
  unsigned char major_opcode;
  unsigned char sub_opcode;
  unsigned char syntax_class = 0;
  unsigned char syntax_class_modifiers = 0;
  unsigned char suffix_class = 0;
  
  insn_name = get_instruction_name();
  
  major_opcode = get_opcode_value(_("expected comma after instruction name"));
  if (!input_line_pointer)
    return;
  
  SKIP_WHITESPACE();
  sub_opcode = get_opcode_value(_("expected comma after major opcode"));
  if (!input_line_pointer)
    return;
  
  SKIP_WHITESPACE();
  if (!expect_comma_and_advance("expected comma after sub opcode"))
    return;
  
  suffix_class = parse_class_with_pipe(suffixclass, ARRAY_SIZE(suffixclass),
                                        sizeof(suffixclass[0]), "invalid suffix class");
  if (!suffix_class && *input_line_pointer == '\0')
    return;
  
  if (!expect_comma_and_advance("expected comma after suffix class"))
    return;
  
  parse_syntax_classes(&syntax_class, &syntax_class_modifiers);
  
  demand_empty_rest_of_line();
  
  einsn->name = insn_name;
  einsn->major = major_opcode;
  einsn->minor = sub_opcode;
  einsn->syntax = syntax_class;
  einsn->modsyn = syntax_class_modifiers;
  einsn->suffix = suffix_class;
  einsn->flags = syntax_class | 
    ((syntax_class_modifiers & ARC_OP1_IMM_IMPLIED) ? ARC_OP1_IMM_IMPLIED_FLAG : 0);
}

/* Generate an extension section.  */

static int
arc_set_ext_seg (void)
{
  if (!arcext_section)
    {
      arcext_section = subseg_new (".arcextmap", 0);
      bfd_set_section_flags (arcext_section, SEC_READONLY | SEC_HAS_CONTENTS);
      return 1;
    }
  
  subseg_set (arcext_section, 0);
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

static void write_byte(char value)
{
    char *p = frag_more(1);
    *p = value;
}

static void write_string(const char *str)
{
    int len = strlen(str) + 1;
    char *p = frag_more(len);
    strcpy(p, str);
}

static void write_instruction_data(extInstruction_t *einsn, int name_len)
{
    write_byte(5 + name_len + 1);
    write_byte(EXT_INSTRUCTION);
    write_byte(einsn->major);
    write_byte(einsn->minor);
    write_byte(einsn->flags);
    write_string(einsn->name);
}

static void create_extinst_section(extInstruction_t *einsn)
{
    segT old_sec = now_seg;
    int old_subsec = now_subseg;
    int name_len = strlen(einsn->name);

    arc_set_ext_seg();
    write_instruction_data(einsn, name_len);
    subseg_set(old_sec, old_subsec);
}

/* Handler .extinstruction pseudo-op.  */

static void validate_opcode_name(const char *name)
{
    if (arc_find_opcode(name))
        as_warn(_("Pseudocode already used %s"), name);
}

static void get_opcode_range_limits(unsigned char *moplow, unsigned char *mophigh)
{
    *moplow = 0x05;
    *mophigh = (selected_cpu.flags & (ARC_OPCODE_ARCv2EM | ARC_OPCODE_ARCv2HS)) ? 0x07 : 0x0a;
}

static void validate_major_opcode(unsigned char major, unsigned char moplow, unsigned char mophigh)
{
    if ((major > mophigh) || (major < moplow))
        as_fatal(_("major opcode not in range [0x%02x - 0x%02x]"), moplow, mophigh);
}

static void validate_minor_opcode(unsigned char minor, unsigned char major)
{
    #define MAX_MINOR_OPCODE 0x3f
    #define MAJOR_OPCODE_5 5
    #define MAJOR_OPCODE_9 9
    #define MAJOR_OPCODE_A 0x0a
    
    if ((minor > MAX_MINOR_OPCODE) && (major != MAJOR_OPCODE_A) && 
        (major != MAJOR_OPCODE_5) && (major != MAJOR_OPCODE_9))
        as_fatal(_("minor opcode not in range [0x00 - 0x3f]"));
}

static void validate_syntax_modifiers(unsigned int syntax, unsigned int modsyn)
{
    switch (syntax & ARC_SYNTAX_MASK)
    {
    case ARC_SYNTAX_3OP:
        if (modsyn & ARC_OP1_IMM_IMPLIED)
            as_fatal(_("Improper use of OP1_IMM_IMPLIED"));
        break;
    case ARC_SYNTAX_2OP:
    case ARC_SYNTAX_1OP:
    case ARC_SYNTAX_NOP:
        if (modsyn & ARC_OP1_MUST_BE_IMM)
            as_fatal(_("Improper use of OP1_MUST_BE_IMM"));
        break;
    default:
        break;
    }
}

static struct arc_opcode *generate_and_validate_opcodes(extInstruction_t *einsn)
{
    const char *errmsg = NULL;
    struct arc_opcode *arc_ext_opcodes;
    
    arc_ext_opcodes = arcExtMap_genOpcode(einsn, selected_cpu.flags, &errmsg);
    
    if (arc_ext_opcodes == NULL)
    {
        if (errmsg)
            as_fatal("%s", errmsg);
        else
            as_fatal(_("Couldn't generate extension instruction opcodes"));
    }
    else if (errmsg)
        as_warn("%s", errmsg);
    
    return arc_ext_opcodes;
}

static void arc_extinsn(int ignore ATTRIBUTE_UNUSED)
{
    extInstruction_t einsn;
    struct arc_opcode *arc_ext_opcodes;
    unsigned char moplow, mophigh;

    memset(&einsn, 0, sizeof(einsn));
    tokenize_extinsn(&einsn);

    validate_opcode_name(einsn.name);
    
    get_opcode_range_limits(&moplow, &mophigh);
    validate_major_opcode(einsn.major, moplow, mophigh);
    validate_minor_opcode(einsn.minor, einsn.major);
    validate_syntax_modifiers(einsn.syntax, einsn.modsyn);
    
    arc_ext_opcodes = generate_and_validate_opcodes(&einsn);
    arc_insert_opcode(arc_ext_opcodes);
    create_extinst_section(&einsn);
}

static bool validate_negative_number(int number, int opertype)
{
  if (number < 0 && opertype != EXT_AUX_REGISTER)
    {
      const char *register_type = (opertype == EXT_CORE_REGISTER) ? 
                                   "extCoreRegister's" : "extCondCode's";
      as_bad(_("%s second argument cannot be a negative number %d"),
             register_type, number);
      ignore_rest_of_line();
      return false;
    }
  return true;
}

static bool expect_comma_after(const char *item_name)
{
  SKIP_WHITESPACE();
  if (*input_line_pointer != ',')
    {
      as_bad(_("expected comma after %s"), item_name);
      ignore_rest_of_line();
      return false;
    }
  input_line_pointer++;
  return true;
}

static char* parse_register_name(void)
{
  char *p;
  char c;
  
  SKIP_WHITESPACE();
  p = input_line_pointer;
  c = get_symbol_name(&p);
  char *name = xstrdup(p);
  restore_line_pointer(c);
  
  return name;
}

static int parse_register_mode(void)
{
  #define MODE_READ_WRITE "r|w"
  #define MODE_READ "r"
  #define MODE_WRITE "w"
  
  char *mode = input_line_pointer;
  int imode;
  
  if (startswith(mode, MODE_READ_WRITE))
    {
      imode = 0;
      input_line_pointer += 3;
    }
  else if (startswith(mode, MODE_READ))
    {
      imode = ARC_REGISTER_READONLY;
      input_line_pointer += 1;
    }
  else if (startswith(mode, MODE_WRITE))
    {
      imode = ARC_REGISTER_WRITEONLY;
      input_line_pointer += 1;
    }
  else
    {
      as_bad(_("invalid mode"));
      ignore_rest_of_line();
      return -1;
    }
  
  return imode;
}

static int parse_core_shortcut(void)
{
  #define SHORTCUT_CANNOT "cannot_shortcut"
  #define SHORTCUT_CAN "can_shortcut"
  #define SHORTCUT_CANNOT_LEN 15
  #define SHORTCUT_CAN_LEN 12
  
  if (startswith(input_line_pointer, SHORTCUT_CANNOT))
    {
      input_line_pointer += SHORTCUT_CANNOT_LEN;
      return ARC_REGISTER_NOSHORT_CUT;
    }
  
  if (!startswith(input_line_pointer, SHORTCUT_CAN))
    {
      as_bad(_("shortcut designator invalid"));
      ignore_rest_of_line();
      return -1;
    }
  
  input_line_pointer += SHORTCUT_CAN_LEN;
  return 0;
}

static bool
tokenize_extregister(extRegister_t *ereg, int opertype)
{
  bool isCore_p = opertype == EXT_CORE_REGISTER;
  bool isReg_p = opertype == EXT_CORE_REGISTER || opertype == EXT_AUX_REGISTER;
  int imode = 0;
  
  char *name = parse_register_name();
  
  if (!expect_comma_after("name"))
    {
      free(name);
      return false;
    }
  
  int number = get_absolute_expression();
  
  if (!validate_negative_number(number, opertype))
    {
      free(name);
      return false;
    }
  
  if (isReg_p)
    {
      if (!expect_comma_after("register number"))
        {
          free(name);
          return false;
        }
      
      imode = parse_register_mode();
      if (imode < 0)
        {
          free(name);
          return false;
        }
    }
  
  if (isCore_p)
    {
      if (!expect_comma_after("register mode"))
        {
          free(name);
          return false;
        }
      
      int shortcut = parse_core_shortcut();
      if (shortcut < 0)
        {
          free(name);
          return false;
        }
      imode |= shortcut;
    }
  
  demand_empty_rest_of_line();
  
  ereg->name = name;
  ereg->number = number;
  ereg->imode = imode;
  return true;
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
write_byte(char value)
{
    char *p = frag_more(1);
    *p = value;
}

static void
write_register_header(int opertype, int name_len)
{
    write_byte(3 + name_len + 1);
    write_byte(opertype);
}

static void
write_aux_register_header(int name_len)
{
    write_byte(6 + name_len + 1);
    write_byte(EXT_AUX_REGISTER);
}

static void
write_32bit_value_as_bytes(int value)
{
    write_byte((value >> 24) & 0xff);
    write_byte((value >> 16) & 0xff);
    write_byte((value >> 8) & 0xff);
    write_byte(value & 0xff);
}

static void
write_core_or_cond_register(extRegister_t *ereg, int opertype, int name_len)
{
    write_register_header(opertype, name_len);
    write_byte(ereg->number);
}

static void
write_aux_register(extRegister_t *ereg, int name_len)
{
    write_aux_register_header(name_len);
    write_32bit_value_as_bytes(ereg->number);
}

static void
write_register_name(const char *name, int name_len)
{
    char *p = frag_more(name_len + 1);
    strcpy(p, name);
}

static void
create_extcore_section(extRegister_t *ereg, int opertype)
{
    segT old_sec = now_seg;
    int old_subsec = now_subseg;
    int name_len = strlen(ereg->name);

    arc_set_ext_seg();

    switch (opertype)
    {
    case EXT_COND_CODE:
    case EXT_CORE_REGISTER:
        write_core_or_cond_register(ereg, opertype, name_len);
        break;
    case EXT_AUX_REGISTER:
        write_aux_register(ereg, name_len);
        break;
    default:
        break;
    }

    write_register_name(ereg->name, name_len);
    subseg_set(old_sec, old_subsec);
}

/* Handler .extCoreRegister pseudo-op.  */

static void
process_core_register(extRegister_t *ereg)
{
  const int MAX_CORE_REGISTER_VALUE = 60;
  
  if (ereg->number > MAX_CORE_REGISTER_VALUE)
    as_bad(_("core register %s value (%d) too large"), ereg->name, ereg->number);
  declare_register(ereg->name, ereg->number);
}

static void
process_aux_register(extRegister_t *ereg)
{
  struct arc_aux_reg *auxr = XNEW(struct arc_aux_reg);
  auxr->name = ereg->name;
  auxr->cpu = selected_cpu.flags;
  auxr->subclass = NONE;
  auxr->address = ereg->number;
  
  if (str_hash_insert(arc_aux_hash, auxr->name, auxr, 0) != NULL)
    as_bad(_("duplicate aux register %s"), auxr->name);
}

static void
add_condition_code(extRegister_t *ereg)
{
  const int MAX_CONDITION_CODE_VALUE = 31;
  const int CONDITION_CODE_BITS = 5;
  const int CONDITION_CODE_SHIFT = 0;
  const int CONDITION_CODE_FAVAIL = 0;
  
  if (ereg->number > MAX_CONDITION_CODE_VALUE)
    as_bad(_("condition code %s value (%d) too large"), ereg->name, ereg->number);
  
  ext_condcode.size++;
  ext_condcode.arc_ext_condcode = 
    XRESIZEVEC(struct arc_flag_operand, ext_condcode.arc_ext_condcode,
               ext_condcode.size + 1);
  
  struct arc_flag_operand *ccode = ext_condcode.arc_ext_condcode + ext_condcode.size - 1;
  ccode->name = ereg->name;
  ccode->code = ereg->number;
  ccode->bits = CONDITION_CODE_BITS;
  ccode->shift = CONDITION_CODE_SHIFT;
  ccode->favail = CONDITION_CODE_FAVAIL;
  ccode++;
  memset(ccode, 0, sizeof(struct arc_flag_operand));
}

static void
arc_extcorereg(int opertype)
{
  extRegister_t ereg;
  
  memset(&ereg, 0, sizeof(ereg));
  if (!tokenize_extregister(&ereg, opertype))
    return;
  
  switch (opertype)
    {
    case EXT_CORE_REGISTER:
      process_core_register(&ereg);
      break;
    case EXT_AUX_REGISTER:
      process_aux_register(&ereg);
      break;
    case EXT_COND_CODE:
      add_condition_code(&ereg);
      break;
    default:
      as_bad(_("Unknown extension"));
      break;
    }
  create_extcore_section(&ereg, opertype);
}

/* Parse a .arc_attribute directive.  */

static void
arc_attribute (int ignored ATTRIBUTE_UNUSED)
{
  int tag = obj_elf_vendor_attribute (OBJ_ATTR_PROC);

  if (tag < NUM_KNOWN_OBJ_ATTRIBUTES)
    attributes_set_explicitly[tag] = true;
}

/* Set an attribute if it has not already been set by the user.  */

static void
arc_set_attribute_int (int tag, int value)
{
  if (tag < 1
      || tag >= NUM_KNOWN_OBJ_ATTRIBUTES
      || !attributes_set_explicitly[tag])
    {
      if (!bfd_elf_add_proc_attr_int (stdoutput, tag, value))
        as_fatal (_("error adding attribute: %s"),
                  bfd_errmsg (bfd_get_error ()));
    }
}

static void
arc_set_attribute_string (int tag, const char *value)
{
  if (tag < 1 || tag >= NUM_KNOWN_OBJ_ATTRIBUTES || !attributes_set_explicitly[tag])
    {
      if (!bfd_elf_add_proc_attr_string (stdoutput, tag, value))
        {
          as_fatal (_("error adding attribute: %s"), bfd_errmsg (bfd_get_error ()));
        }
    }
}

/* Allocate and concatenate two strings.  s1 can be NULL but not
   s2.  s1 pointer is freed at end of this procedure.  */

static char *
arc_stralloc (char * s1, const char * s2)
{
  gas_assert (s2);
  
  int s1_len = s1 ? strlen (s1) : 0;
  int s2_len = strlen (s2);
  int total_len = s1_len + s2_len + (s1 ? 2 : 1);
  
  char * p = xmalloc (total_len);
  
  if (s1)
    {
      sprintf (p, "%s,%s", s1, s2);
      free (s1);
    }
  else
    {
      strcpy (p, s2);
    }
  
  return p;
}

/* Set the public ARC object attributes.  */

static int get_cpu_base_tag(void)
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

static void set_cpu_base_attribute(int base)
{
    if (attributes_set_explicitly[Tag_ARC_CPU_base])
    {
        int current_base = bfd_elf_get_obj_attr_int(stdoutput, OBJ_ATTR_PROC, Tag_ARC_CPU_base);
        if (base != current_base)
            as_warn(_("Overwrite explicitly set Tag_ARC_CPU_base"));
    }
    
    if (!bfd_elf_add_proc_attr_int(stdoutput, Tag_ARC_CPU_base, base))
        as_fatal(_("error adding attribute: %s"), bfd_errmsg(bfd_get_error()));
}

static void set_osabi_attribute(void)
{
    if (attributes_set_explicitly[Tag_ARC_ABI_osver])
    {
        int val = bfd_elf_get_obj_attr_int(stdoutput, OBJ_ATTR_PROC, Tag_ARC_ABI_osver);
        selected_cpu.eflags = ((selected_cpu.eflags & ~EF_ARC_OSABI_MSK) | (val & 0x0f << 8));
    }
    else
    {
        arc_set_attribute_int(Tag_ARC_ABI_osver, E_ARC_OSABI_CURRENT >> 8);
    }
}

static char* build_isa_config_string(void)
{
    char *s = NULL;
    unsigned int i;
    
    for (i = 0; i < ARRAY_SIZE(feature_list); i++)
        if (selected_cpu.features & feature_list[i].feature)
            s = arc_stralloc(s, feature_list[i].attr);
    
    return s;
}

static void set_rf16_attribute(void)
{
    if (!attributes_set_explicitly[Tag_ARC_ABI_rf16])
        return;
    
    if (!bfd_elf_get_obj_attr_int(stdoutput, OBJ_ATTR_PROC, Tag_ARC_ABI_rf16))
        return;
    
    if (rf16_only)
        return;
    
    as_warn(_("Overwrite explicitly set Tag_ARC_ABI_rf16 to full register file"));
    if (!bfd_elf_add_proc_attr_int(stdoutput, Tag_ARC_ABI_rf16, 0))
        as_fatal(_("error adding attribute: %s"), bfd_errmsg(bfd_get_error()));
}

static void arc_set_public_attributes(void)
{
    char *isa_config_str;
    
    arc_set_attribute_string(Tag_ARC_CPU_name, selected_cpu.name);
    
    set_cpu_base_attribute(get_cpu_base_tag());
    
    set_osabi_attribute();
    
    arc_check_feature();
    
    isa_config_str = build_isa_config_string();
    if (isa_config_str)
        arc_set_attribute_string(Tag_ARC_ISA_config, isa_config_str);
    
    arc_set_attribute_int(Tag_ARC_ISA_mpy_option, mpy_option);
    arc_set_attribute_int(Tag_ARC_ABI_pic, pic_option);
    arc_set_attribute_int(Tag_ARC_ABI_sda, sda_option);
    arc_set_attribute_int(Tag_ARC_ABI_tls, tls_option);
    arc_set_attribute_int(Tag_ARC_ATR_version, 1);
    
    set_rf16_attribute();
}

/* Add the default contents for the .ARC.attributes section.  */

void
arc_md_finish (void)
{
  arc_set_public_attributes ();

  if (!bfd_set_arch_mach (stdoutput, bfd_arch_arc, selected_cpu.mach))
    as_fatal (_("could not set architecture and machine"));

  bfd_set_private_flags (stdoutput, selected_cpu.eflags);
}

void arc_copy_symbol_attributes(symbolS *dest, symbolS *src)
{
  ARC_GET_FLAG(dest) = ARC_GET_FLAG(src);
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
#define T(tag) {#tag, tag}
    T(Tag_ARC_PCS_config),
    T(Tag_ARC_CPU_base),
    T(Tag_ARC_CPU_variation),
    T(Tag_ARC_CPU_name),
    T(Tag_ARC_ABI_rf16),
    T(Tag_ARC_ABI_osver),
    T(Tag_ARC_ABI_sda),
    T(Tag_ARC_ABI_pic),
    T(Tag_ARC_ABI_tls),
    T(Tag_ARC_ABI_enumsize),
    T(Tag_ARC_ABI_exceptions),
    T(Tag_ARC_ABI_double_size),
    T(Tag_ARC_ISA_config),
    T(Tag_ARC_ISA_apex),
    T(Tag_ARC_ISA_mpy_option),
    T(Tag_ARC_ATR_version)
#undef T
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
