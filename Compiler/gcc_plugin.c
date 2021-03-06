
#include "gcc-plugin.h"
#include "plugin-version.h"
#include <coretypes.h>

#include "tm.h"
#include <tree.h>
#include <tree-pass.h>
#include <tree-core.h>
#include <print-tree.h>
#include <tree-ssa-alias.h>
#include "gimple.h"
#include "gimple-iterator.h"
#include "tree-inline.h"

#include "cgraph.h"
#include "gimple-walk.h"
#include "gimple-pretty-print.h"
#include "gimple-ssa.h"
#include "context.h"
#include "tree-dfa.h"
#include "attribs.h"

#include "config.h"
#include "system.h"
#include <coretypes.h>
#include "insn-constants.h"
#include "options.h"
#include "backend.h" 
#include "rtl.h"
#include "alloc-pool.h"
#include "ssa.h"
#include "diagnostic-core.h"
#include "fold-const.h"
#include "stor-layout.h"
#include "stmt.h"
#include "ssa-iterators.h"
//#include "DFS.h"
#include "Algorithm.h"
#include "tree-pass.h"
#include "hash-map.h"

int plugin_is_GPL_compatible;



struct register_pass_info inline_passinfo;
struct register_pass_info detect_passinfo;

const pass_data inline_pass_data =
{
  GIMPLE_PASS, 			/* type */
  "inline_pass", 			/* name */
  OPTGROUP_INLINE, 		/* optinfo_flags */
  TV_NONE, 				/* tv_id */
  0, 					/* properties_required */
  0, 					/* properties_provided */
  0, 					/* properties_destroyed */
  0, 					/* todo_flags_start */
  0, 					/* todo_flags_finish */
};
const pass_data detect_pass_data =
{
    .type = SIMPLE_IPA_PASS,//SIMPLE_IPA_PASS,GIMPLE_PASS
    .name = "my_pass6",
    .optinfo_flags = OPTGROUP_NONE,
    .tv_id = TV_NONE,
    .properties_required = PROP_ssa,
    .properties_provided = 0,
    .properties_destroyed = 0,
    .todo_flags_start = 0,
    .todo_flags_finish = 0
};
static int test_always(void){
			insert_always_inline();
			//fprintf(stderr,"=======end=========\n");
			return false;
}
namespace {
class pass_ipa_always : public ipa_opt_pass_d
{
public:
  pass_ipa_always (gcc::context *ctxt)
    : ipa_opt_pass_d (inline_pass_data, ctxt,
                      NULL, /* generate_summary */
                      NULL, /* write_summary */
                      NULL, /* read_summary */
                      NULL, /* write_optimization_summary */
                      NULL, /* read_optimization_summary */
                      NULL, /* stmt_fixup */
                      0, /* function_transform_todo_flags_start */
                      0, /* function_transform */
                      NULL) /* variable_transform */
  {}
  /* opt_pass methods: */
  virtual unsigned int execute (function *) { return test_always (); }
  virtual pass_ipa_always* clone() override { return this; }
}; // class pass_ipa_inline
}
ipa_opt_pass_d *
make_pass_ipa_always (gcc::context *ctxt)
{
  return new pass_ipa_always (ctxt);
}


static int execute_detect(void){
			detect();
			return 0;
}
namespace {
class pass_ipa_detect : public ipa_opt_pass_d
{
public:
  pass_ipa_detect (gcc::context *ctxt)
    : ipa_opt_pass_d (detect_pass_data, ctxt,
                      NULL, /* generate_summary */
                      NULL, /* write_summary */
                      NULL, /* read_summary */
                      NULL, /* write_optimization_summary */
                      NULL, /* read_optimization_summary */
                      NULL, /* stmt_fixup */
                      0, /* function_transform_todo_flags_start */
                      0, /* function_transform */
                      NULL) /* variable_transform */
  {}
  /* opt_pass methods: */
  virtual unsigned int execute (function *) { return execute_detect (); }
  virtual pass_ipa_detect* clone() override { return this; }
}; // class pass_ipa_inline
}
ipa_opt_pass_d *
make_pass_detect (gcc::context *ctxt)
{
  return new pass_ipa_detect (ctxt);
}
int plugin_init(struct plugin_name_args *plugin_info, struct plugin_gcc_version *version)
{
    fp = fopen ("file.txt", "a");
	fprintf(fp,"test\n");
	if (!plugin_default_version_check(version, &gcc_version)){
		printf("incompatible gcc/plugin versions\n");
		return 1;
	}
	inline_passinfo.pass=make_pass_ipa_always(g);
	inline_passinfo.reference_pass_name="einline";
	inline_passinfo.ref_pass_instance_number=0;
	inline_passinfo.pos_op=PASS_POS_INSERT_BEFORE;


	detect_passinfo.pass=make_pass_detect(g);
	detect_passinfo.reference_pass_name="pta";
	detect_passinfo.ref_pass_instance_number=0;
	detect_passinfo.pos_op=PASS_POS_INSERT_AFTER;

	const char * const plugin_name = plugin_info->base_name;

	register_callback("test5", PLUGIN_PASS_MANAGER_SETUP, NULL, &inline_passinfo);
	register_callback("test6", PLUGIN_PASS_MANAGER_SETUP, NULL, &detect_passinfo);
    
    return 0;
}


