#include "config.h"
#include "system.h"
#include <coretypes.h>
#include "insn-constants.h"
//#include "config/i386/i386.h"
#include "is-a.h"
#include "options.h"
#include "backend.h" 
#include "rtl.h"
#include "tree-pass.h"
#include "tree.h"
#include "gimple.h"
#include "alloc-pool.h"
#include "ssa.h"
#include "cgraph.h"
#include "tree-pretty-print.h"
#include "diagnostic-core.h"
#include "fold-const.h"
#include "stor-layout.h"
#include "stmt.h"
#include "gimple-iterator.h"
#include "tree-into-ssa.h"
#include "tree-dfa.h"
#include "params.h"
#include "gimple-walk.h"
#include "varasm.h"
#include "options.h"
#include "gimple-pretty-print.h"
#include "print-tree.h"
#include <string.h>
#include "intl.h"
#include "dominance.h"
#include <et-forest.h>
#include <cgraph.h>
/*Algorithm 3*/
#include "DFS.h"
#include "cfgloop.h"
#include <vector>
#define FOR_EACH_TABLE(TABLE,TAR)\
	for((TAR)=((TABLE)==NULL)?NULL:(TABLE)->target;\
	(TAR)!=NULL;\
	(TABLE)=(TABLE)->next,(TAR)=((TABLE)==NULL)?NULL:(TABLE)->target)
#define FOR_EACH_USE_TABLE(USE,STMT)\
	for((STMT)=((USE)==NULL)?NULL:(USE)->stmt;(USE)!=NULL;(USE)=(USE)->next,(STMT)=((USE)==NULL)?NULL:(USE)->stmt)

/*allocation and deallocation table*/
struct ptb{
	tree target;      // debug_tree  debug_head
	location_t loc;		// warning_at
	ptb *next;			//print_pointer_table_new
	int state;			
	bool may_realloc, is_phi_stmt;
	gimple *last_stmt;
	basic_block bb;   //bb->index
	cgraph_node *node;	
	gimple* caller; //
	function *fun;
	bool removed;
	bool inbranch;
};

ptb start1, start2, start3, start4, start5, start6,start7; 
ptb *ptable, *retable, *ftable, *phitable,*return_table,*use_table,*fopen_table;

struct gimple_array
{
	gimple *stmt;
	tree aptr;
	gimple_array *next;
};

/*function decl tree and rhs tree*/
struct fdecl{
	tree fndecl;
	tree fn;
	gimple *g;
};

/*function decl and location*/
struct var_points_to{
	vector<vector<pair<fdecl,location_t>>> may_malloc_path;
	tree decl;
};


/*record each DFS graph*/
hash_map<cgraph_node*, Graph > *fDFS;

/*use function tree search cgraph_node*/
hash_map<tree, cgraph_node *> *fnode;

/*rhs function search function decl and location*/
hash_map<tree,var_points_to> *tvpt;

/*state*/
unsigned int POINTER_NOT_EXIST        	= 0;
unsigned int POINTER_STATE_IS_FREE    	= 1;
unsigned int POINTER_STATE_IS_NORMAL  	= 2;
unsigned int POINTER_STATE_IS_MALLOC  	= 3;
unsigned int POINTER_STATE_IS_FILE    	= 4;
unsigned int POINTER_STATE_MAY_IS_FREE	= 5;

const unsigned int POINTER_NOT        = 0;
const unsigned int POINTER_MAY        = 1;
const unsigned int POINTER_MUST       = 2;
/*dump file */
FILE * fp;

/*interprocedural analysis*/
bool ipa=false;

/*main function*/
function* main_fun;
cgraph_node* main_node;


bool bb_in_branch_p(ptb *table){
	return !dominated_by_p(CDI_DOMINATORS,table->fun->cfg->x_exit_block_ptr->prev_bb,table->bb);
}

bool bb_in_branch_p(gimple* stmt){
	//function* fn = DECL_STRUCT_FUNCTION(gimple_get_lhs(stmt));
	return !dominated_by_p(CDI_DOMINATORS,stmt->bb,cfun->cfg->x_exit_block_ptr->prev_bb);
}


void init_table(){
	//fprintf(stderr,"init_table.... \n");
	start1.target = NULL_TREE;
	start1.next = NULL;
	start1.state = POINTER_NOT_EXIST;
	ptable = &start1;

	start2.target = NULL_TREE;
	start2.next = NULL;
	start2.state = POINTER_NOT_EXIST;
	ftable = &start2;

	start3.target = NULL_TREE;
	start3.next = NULL;
	start3.state = POINTER_NOT_EXIST;
	retable = &start3;

	start4.target = NULL_TREE;
	start4.next = NULL;
	start4.state = POINTER_NOT_EXIST;
	phitable = &start4;

	start5.target = NULL_TREE;
	start5.next = NULL;
	start5.state = POINTER_NOT_EXIST;
	return_table = &start5; 


	start6.target = NULL_TREE;
	start6.next = NULL;
	start6.state = POINTER_NOT_EXIST;
	use_table = &start6;

	start7.target = NULL_TREE;
	start7.next = NULL;
	start7.state = POINTER_NOT_EXIST;
	fopen_table = &start7;
}

/*set allocation and deallocation table*/
void set_ptb(basic_block b,ptb *table, tree t, location_t l, int s, gimple *stmt,cgraph_node *node){
	if(table->target == NULL_TREE){
		table->bb = b;
		table->target = t;
		table->next = NULL;
		table->loc = l;
		table->state = s;
		table->may_realloc = false;
		table->last_stmt = stmt;
		table->node=node;
		table->inbranch=bb_in_branch_p(stmt);
		table->fun=node->get_fun();
		if(gimple_code (stmt) == GIMPLE_PHI){
			//fprintf(stderr, "add phi stmt ");debug_head(table->target);
		}
		table->removed=false;
	}  
	else{
		while(table->next!=NULL){
			table=table->next;
		}
		table->next = new ptb();
		table = table->next;
		table->bb = b;
		table->target = t;
		table->next = NULL;
		table->loc = l;
		table->state = s;
		table->may_realloc = false;
		table->last_stmt = stmt;
		table->node=node;
		table->inbranch=bb_in_branch_p(stmt);
		table->fun=node->get_fun();
		if(gimple_code (stmt) == GIMPLE_PHI){
			//fprintf(stderr, "add phi stmt ");debug_head(table->target);
			table->is_phi_stmt = true;
		}
		else
			table->is_phi_stmt = false;
		table->removed=false;
	}
}

void set_gimple_array(gimple_array *table, gimple *used_stmt,tree a){
	if(table->stmt==NULL){
		table->stmt = used_stmt;
		table->aptr=a;
		table->next=NULL;
	}else{
		bool same=false;
		while(table->next != NULL){
			if(table->stmt == used_stmt && LOCATION_LINE(gimple_location(table->stmt)) == LOCATION_LINE(gimple_location(used_stmt))){
				same=true;
				break;
			}
			table = table->next;
		}
		if(!same){
			table->next = new gimple_array();
			table = table->next;
			table->stmt = used_stmt;
			table->aptr=a;
			table->next = NULL;
		}
	}
}
/*Algorithm 4*/
void search_imm_use(gimple_array *used_stmt, tree target){
	imm_use_iterator imm_iter;
	gimple_array *used2=used_stmt;
	gimple *use_stmt; 
	gimple *gc;
	FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, target)
	{
		//debug_gimple_stmt(use_stmt);
		if(gimple_code(use_stmt) == GIMPLE_ASSIGN){
			//debug_tree(gimple_assign_lhs(use_stmt));
			if(gimple_assign_lhs(use_stmt) && TREE_CODE(gimple_assign_lhs(use_stmt))==SSA_NAME && gimple_assign_single_p(use_stmt)){
				set_gimple_array(used_stmt, use_stmt,target);
				search_imm_use(used_stmt, gimple_assign_lhs(use_stmt));
			}
		} 
		else if(gimple_code(use_stmt) == GIMPLE_PHI){
			if(gimple_phi_result(use_stmt) && TREE_CODE(gimple_phi_result(use_stmt))==SSA_NAME){
				//debug_gimple_stmt(use_stmt);
				//debug_tree(gimple_phi_result(use_stmt));
				bool exist=false;
				FOR_EACH_USE_TABLE(used2,gc){

					//debug_gimple_stmt(gc);
					if(gc==use_stmt){
						exist=true;
					}
				}
				if(!exist){
					set_gimple_array(used_stmt, use_stmt,target);
					search_imm_use(used_stmt, gimple_phi_result(use_stmt));
				}
			}
			
		}else{
			set_gimple_array(used_stmt, use_stmt,target);
		}
		
  }
}

void print_path(vector<pair<fdecl ,location_t>> *path){
	fprintf(stderr,"malloc from ->\n");
	for(int i=0;i<(*path).size();i++)
		fprintf(stderr,"	function ->%s in loc %d \n",IDENTIFIER_POINTER (DECL_NAME((*path)[i].first.fndecl)),LOCATION_LINE((*path)[i].second));
	
}

bool path_intersection(vector<pair<fdecl,location_t>> *path,tree t,location_t loc){
	for(int i=0;i<(*path).size();i++){
		if((*path)[i].first.fndecl == t  && (*path)[i].second==loc){
			//fprintf(stderr,"intersection\n");
			return true;
		}
	}
	return false;
}

bool path_intersection_tvpt(vector<pair<fdecl,location_t>> path,vector<pair<fdecl,location_t>> path2){
	vector<pair<fdecl,location_t>> temp;
	int ii=0;
	if (path.size()<path2.size()){
		temp=path2;
		path2=path;
		path=temp;
	}
	for(int i=0;i<path.size();){
		if(path.size()-i<path2.size())
			return false;

		//fprintf(stderr,"=path_intersection_tvpt= ii=%d i=%d\n",ii,i);
		//fprintf(stderr,"=path1ptr  %s  %d=\n",IDENTIFIER_POINTER (DECL_NAME(path[i+ii].first.fndecl)),LOCATION_LINE(path[i+ii].second));
		//fprintf(stderr,"=path2ptr  %s  %d=\n",IDENTIFIER_POINTER (DECL_NAME(path2[ii].first.fndecl)),LOCATION_LINE(path2[ii].second));

		if(path[i+ii].first.fndecl == path2[ii].first.fndecl){
			if(path[i+ii].second == path2[ii].second){
				if(ii==path2.size()-1)
					return true;
				ii++;
				continue;
			}
		}
		if(ii>0)
			ii=0;
		return false;
	}
	return false;
}

void print_tvpt(tree a){
	if(tvpt->get(a)==NULL)
		return ;
	var_points_to vpt=*(tvpt->get(a));
	vector<vector<pair<fdecl,location_t>>> path=vpt.may_malloc_path;
	vector<pair<fdecl,location_t>> loc;
	fprintf(stderr,"			=======print_tvpt %d   %d========\n",a,path.size());
	for(int i=0;i<path.size();i++){
		print_path(&path[i]);
	}

}

bool same_path(tree t1,tree t2){
	if(tvpt->get(t1)==NULL || tvpt->get(t2)==NULL)
		return false;
	var_points_to vpt=*(tvpt->get(t1));
	var_points_to vpt2=*(tvpt->get(t2));
	int ii=0;
	vector<vector<pair<fdecl,location_t>>> path=vpt.may_malloc_path;
	vector<vector<pair<fdecl,location_t>>> path2=vpt2.may_malloc_path;

	for(int i=0;i<path.size();i++){
		for(int j=0;j<path2.size();j++){
			if (path_intersection_tvpt(path[i],path2[j])){
				return true;
			}
		}
	}
	return false;
	
	
}
void tracer_caller(cgraph_node *dest,cgraph_node *current,vector<pair<fdecl ,location_t>> *path,bool only_track){
	//fprintf(stderr,"======dest:%s current:%s\n",function_name (DECL_STRUCT_FUNCTION(dest->decl)),function_name (DECL_STRUCT_FUNCTION(current->decl)));
	//debug_tree(current->decl);
	cgraph_node *ftn;
	cgraph_node* node2;
	for (cgraph_edge *e = current->callers; e; e = e->next_caller){
		fdecl fd;
		gimple *ga=e->call_stmt;
		debug_gimple_stmt(ga);

		tree a=gimple_call_fn(ga);
		//debug_tree(a);
		fd.fn=a;
		tree b=gimple_call_fndecl(ga);
		fd.fndecl=b;
		fd.g=ga;
		function *f;
		f=DECL_STRUCT_FUNCTION(gimple_call_fndecl(ga));

		location_t loc;
		loc=gimple_location(ga);
		
		//debug_head(a);
		if(f!=NULL){
			if(!path_intersection(path,b,loc)){
				vector<pair<fdecl ,location_t>> next=*path;
				next.push_back(make_pair(fd,loc));

				//print_path(&next);
				//debug_head(a);

				node2=*(fnode->get(a));
				ftn=node2;
				if(dest->decl == ftn->decl){
					tree lhs=gimple_call_lhs (ga);
					print_path(&next);
					debug_head(gimple_call_lhs (ga));

					var_points_to a=*(tvpt->get(lhs));
					a.may_malloc_path.push_back(next);
					tvpt->put(lhs,a);

					continue;
				}
				if(gimple_call_lhs(ga)!=NULL){
					tree lhs=gimple_call_lhs(ga);
					gimple_array start;
					gimple* stmt;
					start.stmt=NULL;
					gimple_array *used_stmt=&start;
					search_imm_use(used_stmt, lhs);
					FOR_EACH_USE_TABLE(used_stmt,stmt){
						//gimple_bb(SSA_NAME_DEF_STMT (gimple_phi_arg_def(phi, i))
						if(gimple_code(stmt) == GIMPLE_RETURN){
							tracer_caller(dest,ftn,&next,false);
						}else if(only_track){
							tracer_caller(dest,ftn,&next,false);
						}
					}
				}
			}
		}
	}
}

void search_all_path(ptb *free_t,ptb *malloc_t){
	vector<pair<fdecl,location_t>> path;
	tracer_caller(free_t->node,malloc_t->node,&path,false);
}

bool bb_in_same_loop_alloc_free(basic_block m,basic_block f){
	if(m->loop_father->header->index ==f->loop_father->header->index)
		if(m->loop_father->header->index!=0)
			return true;
	return false;
}

bool bb_in_loop_p(basic_block bb){
	return bb->loop_father->header->index!=0;
}


bool Location_b(gimple * a,gimple * b,basic_block bb){
	gimple *gc;
	//debug_gimple_stmt(a);
	//debug_gimple_stmt(b);
	for (gimple_stmt_iterator gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
	{
		gc = gsi_stmt (gsi);
		//debug_gimple_stmt(gc);
		if (gc == a){
			return true;
		}else if(gc == b){
			return false;
		}
	}
	return false;
}
/*Algorithm 5*/
void new_use_after_free_analysis(ptb *ptable, ptb *ftable){
	
  	ptb *table1 = ptable;
  	ptb *table3 = ftable;
	bool to_remove=false;
	tree t;
	struct ptr_info_def* pi;
	struct pt_solution* pt;
	fprintf(stderr,"start use after free analysis\n");
  	FOR_EACH_TABLE(table3,t){
		if(table3->removed || !TREE_CODE(t)==SSA_NAME )
			continue;
		pi= SSA_NAME_PTR_INFO (table3->target);
		pt=&pi->pt;
		//if(pt->null)
			//continue;
		//fprintf(stderr,"---free_table-----\n");
		//debug_head(table3->target);
		gimple_array start;
		start.stmt=NULL;
		gimple_array *used_stmt=&start;

		search_imm_use(used_stmt, table3->target);
		tree t2;
		FOR_EACH_TABLE(table1,t2){
			if(TREE_CODE(table1->target)!=SSA_NAME)
				continue;
			if(ptr_derefs_may_alias_p(table3->target, table1->target)){
				search_imm_use(used_stmt, table1->target);
			}
		}
		table1 = ptable;


		//pointer1
		gimple *u_stmt;
		//fprintf(stderr,"=====free: ");
		//debug_head(table3->target);
		FOR_EACH_USE_TABLE(used_stmt,u_stmt){
			//debug_gimple_stmt(u_stmt);
			if(gimple_code (used_stmt->stmt) ==GIMPLE_PHI )
				continue;
			if( gimple_call_builtin_p (used_stmt->stmt, BUILT_IN_FREE))
				continue;
			//fprintf(stderr,"-----  %d ~ %d \n",table3->bb->index,gimple_bb(used_stmt->stmt)->index);
			//fprintf(stderr,"free line : %d ,use line : %d \n",LOCATION_LINE((table3->loc)),LOCATION_LINE(gimple_location(used_stmt->stmt)));
			//fprintf(stderr,"free bb : %d ,use bb : %d \n",table3->bb->index,gimple_bb(used_stmt->stmt)->index);
			if(table3->bb->index == gimple_bb(used_stmt->stmt)->index){
				if(Location_b(table3->last_stmt,used_stmt->stmt,table3->bb)){  //LOCATION_LINE((table3->loc))<=LOCATION_LINE(gimple_location(used_stmt->stmt))
					//warning_at(table3->loc, 0, "");
					//debug_head(table3->target);
					//fprintf(stderr,"--index : %d %d---\n",table3->bb->index,gimple_bb(used_stmt->stmt)->index);
					if(!table3->removed){
						warning_at(table3->loc, 0, "Use after free error!: free location");
						warning_at(gimple_location(used_stmt->stmt), 0, "use location");///ppp
						//fprintf(fp,"%s use after free\n",gimple_filename (table3->last_stmt));
						//remove_pointer_stmt(table3->last_stmt);
						//table3->removed=true;
					}
				}
			}else if(fDFS->get(table3->node)->is_succ(table3->bb,gimple_bb(used_stmt->stmt))){
				//fprintf(stderr,"----- is_succ\n");
				if(!table3->removed){
					warning_at(table3->loc, 0, "Use after free error!: free location");
					warning_at(gimple_location(used_stmt->stmt), 0, "use location");
					//fprintf(fp,"%s use after free \n",DECL_SOURCE_FILE (table3->fun->decl));
					//remove_pointer_stmt(table3->last_stmt);
					//table3->removed=true;
				}
			}
		}	
		//fprintf(stderr,"=====use table end \n");
	}
}

void new_memory_leak_analysis (ptb *ptable, ptb *ftable){
	fprintf(stderr, "start memory_leak_analysis\n");
	ptb *table1 = ptable;
	ptb *table3 = ftable;
	tree t,t2;
	int may=0;
	int must=0;
	int total=0;
	struct ptr_info_def* pi;
	struct pt_solution* pt;

	struct ptr_info_def *pi1;
	struct pt_solution *pt1;
		
	struct ptr_info_def *pi2;
	struct pt_solution *pt2;

	struct ptr_info_def *pi3;
	struct pt_solution *pt3;
  //phase1 check every alloc pair with one free
	FOR_EACH_TABLE(table1,t){
		if(TREE_CODE(TREE_TYPE(t)) == METHOD_TYPE 
		|| TREE_CODE(TREE_TYPE(t)) == FUNCTION_TYPE
		|| TREE_CODE(TREE_TYPE(t)) == RECORD_TYPE
		|| !(TREE_CODE(t) == SSA_NAME)){
			continue;
		}
		//debug_head(t);
		pi1=SSA_NAME_PTR_INFO (table1->target);  
		pt1=&pi1->pt;
		//if(MAIN_NAME_P(DECL_NAME (table1->node->decl)))
		if(pt1==NULL)
			continue;
		/*Algorithm 6*/
		FOR_EACH_TABLE(table3,t2){
			if(table3->removed){
				continue;
			}
			if(t2==NULL){
				break;
			}
			if(TREE_CODE(table3->target)!=SSA_NAME){
				continue;
			}
			pi2=SSA_NAME_PTR_INFO (table3->target);
			pt2=&pi2->pt;
			//if(pt->null)
				//continue;
				//if(table1->state == POINTER_STATE_IS_FREE)
				//	warning_at(table1->loc, 0,"Memory Leak error");
			if(pt2->vars==NULL)
				continue;
			if(bitmap_intersect_p(pt1->vars,pt2->vars)){
				if(bb_in_loop_p(table1->bb) && !bb_in_same_loop_alloc_free(table1->bb,table3->bb)){
					warning_at(table1->loc, 1, "May Memory-Leak Error!: This alloc statement is in a loop which may cause a memory-leak error.");
					break;
				}

				//warning_at(table1->loc,0,"");
				//fprintf(stderr,"malloc ");debug(pt1);
				//debug_head(t);
				
				//warning_at(table3->loc,0,"");
				//fprintf(stderr,"free ");debug(pt2);
				//debug_head(t2);
		
				//fprintf(stderr,"\n\n");
				
				gimple *def_stmt = SSA_NAME_DEF_STMT (table3->target);
				//debug_tree(table3->target);	
				if(table3->inbranch){
					if(table1->state != POINTER_STATE_IS_FREE){
						//fprintf(stderr,"inbranch \n");
						table1->state = POINTER_STATE_MAY_IS_FREE;
					}
				}else{
					/*Algorithm 7*/
					//debug_gimple_stmt(def_stmt);
					if(gimple_code (def_stmt) == GIMPLE_PHI){
						for(unsigned i=0;i<gimple_phi_num_args(def_stmt);i++){
							tree argu=gimple_phi_arg_def(def_stmt,i);
							//fprintf(stderr,"phi_argu:%d ",i);
							//debug_tree(argu);
							pi3=get_ptr_info (argu);
							pt3=&pi3->pt;
							if(pt3->vars==NULL)
								continue;
							if(!bitmap_intersect_p(pt2->vars,pt3->vars)){
								table1->state = POINTER_STATE_MAY_IS_FREE;
							}
						}
					}else{
						table1->state = POINTER_STATE_IS_FREE;
					}
				}
			}
		}
		if(table1->state != POINTER_STATE_IS_FREE){
			if(table1->state != POINTER_STATE_MAY_IS_FREE){
				warning_at(table1->loc, 0,"Memory Leak Error!");
				must++;
				//debug_tree();
				//debug_head();				
				//debug_tree();
				//fprintf(fp,"%s Memory Leak Error \n",DECL_SOURCE_FILE (table1->fun->decl)); //ppp
				//add_free_stmt(table1, table1->target);
				table1->state = POINTER_STATE_IS_FREE;
			}
			else{
				warning_at(table1->loc, 0,"May Memory Leak Error!");
				may++;
				//fprintf(fp,"%s Memory Leak Error \n",DECL_SOURCE_FILE (table1->fun->decl));
				table1->state = POINTER_STATE_IS_FREE;

			}
		}
		//fprintf(fp,"malloc: %d ",table1->loc);
		total++;
		table3 = ftable;
	}//phase1 end
	table1 = ptable;
	table3 = ftable;
	if(ptable->target!=NULL){
		//fprintf(fp,"%s Memory Leak Error \n",DECL_SOURCE_FILE (table1->fun->decl));
		//fprintf(fp,"%s Memory Leak Error \n		Total:%d\n		May:%d\n		Must:%d\n",DECL_SOURCE_FILE (ptable->fun->decl),total,may,must);
	}else{
		//fprintf(fp,"Memory Leak Error \n		Total:%d\n		May:%d\n		Must:%d\n",total,may,must);
	}  
}

/*Algorithm 10*/


bool path_intersection_1(vector<pair<fdecl,location_t>> path,vector<pair<fdecl,location_t>> path2){
	vector<pair<fdecl,location_t>> temp;
	cgraph_node *node;

	for(int i=0;i<path.size();i++){
		for(int j=0;i<path2.size();j++){
			if(path[i].first.fndecl == path2[j].first.fndecl){
				node=*(fnode->get(path[i].first.fn));
				if(fDFS->get(node)->is_succ(gimple_bb(path[i].first.g),gimple_bb(path2[j].first.g))){
					return true;
				}
			}
		}
	}
	return false;
}
bool intersection_1(tree t1,tree t2){
	if(tvpt->get(t1)==NULL || tvpt->get(t2)==NULL)
		return false;
	var_points_to vpt=*(tvpt->get(t1));
	var_points_to vpt2=*(tvpt->get(t2));
	int ii=0;
	vector<vector<pair<fdecl,location_t>>> path=vpt.may_malloc_path;
	vector<vector<pair<fdecl,location_t>>> path2=vpt2.may_malloc_path;

	for(int i=0;i<path.size();i++){
		for(int j=0;j<path2.size();j++){
			if (path_intersection_1(path[i],path2[j])){
				return true;
			}
		}
	}
	return false;
	
	
}

bool from_different_function(ptb *f1,ptb *f2){
	if(main_node!=NULL){
		vector<pair<fdecl,location_t>> path;
		vector<pair<fdecl,location_t>> path2;
		tracer_caller(main_node,f1->node,&path,true);
		tracer_caller(main_node,f2->node,&path2,true);
	
		return intersection_1(f1->target,f2->target);
	}
	return false;
}

void new_double_free_analysis(ptb *ptable, ptb *ftable){
	
	fprintf(stderr, "start double_free_analysis\n");
	ptb *malloc_t=ptable;
  	ptb *free_t=ftable;
  	ptb *free3_t=ftable;
  	ptb *free2_t;
	tree t,t2,t3;

	int may=0;
	int must=0;
	int total=0;
	gimple_array start;
	start.stmt=NULL;
	gimple_array *used_stmt=&start;
	struct ptr_info_def* pi;
	struct pt_solution* pt;
	struct ptr_info_def* pi2;
	struct pt_solution* pt2;
	//search_imm_use(used_stmt, malloc_t->target);
	/*Algorithm 8*/
	FOR_EACH_TABLE(free_t,t){
			//debug_head(t);
			total++;
    		if(TREE_CODE(free_t->target)!=SSA_NAME){
      			if(free_t->next!=NULL){
        			continue;
      			}
      			else{
        			break;
      			}
    		}
			pi= SSA_NAME_PTR_INFO (free_t->target);
			pt=&pi->pt;
			//debug(pt);
			if(pt->vars==NULL){
				
				fprintf(stderr,"points to is null\n");
				continue;
			}
			if(free_t->bb->loop_father->header->index!=0){
				warning_at(free_t->loc,0,"May Double Free Error!: This free statement is in a loop which may cause a double-free error.");
				may++;
				fprintf(stderr,"%s \n",get_name(free_t->node->decl));
				//fprintf(fp,"%s May Double Free Error: This free statement is in a loop which may cause a double-free error.\n",DECL_SOURCE_FILE (main_fun->decl));
				//continue;
			}
			//fprintf(stderr,"=======loop after========\n");
      		if(free_t->next!=NULL){
				//fprintf(stderr,"=======free2_t=free_t->next========\n");
        		free2_t=free_t->next;
      		}else{
				//fprintf(stderr,"=======break========\n");
				break;
			}
			//fprintf(stderr,"=======ftable2 before========\n");
    		FOR_EACH_TABLE(free2_t,t2){
				//debug_head(t2);
      			if(TREE_CODE(free2_t->target)!=SSA_NAME){
        			if(free2_t->next!=NULL){
            				continue;
        			}
        			else{
						break;
        			}
      			}
				pi2= SSA_NAME_PTR_INFO (free2_t->target);
				pt2=&pi2->pt;
				//debug(pt2);
				//if(pt->null)
					//continue;
				unsigned int errorm=POINTER_NOT;
				if(free_t->bb->loop_father->header->index!=0){
					//fprintf(stderr,"bb_loop_header_p is exist\n");
					//warning_at(free_t->loc,0,"May Double-Free Error: This free statement is in a loop which may cause a double-free error.");
				}
				
				//fprintf(stderr,"	=======search ftable2========\n");
				errorm=POINTER_NOT;
				if(bitmap_intersect_p(pt->vars,pt2->vars)){
					//fprintf(stderr,"	=======bitmap_intersect_p========\n");
					
					if(free_t->fun==free2_t->fun){
						push_cfun(free_t->fun);
						calculate_dominance_info(CDI_DOMINATORS);
						dominated_by_p(CDI_DOMINATORS,free2_t->bb,free_t->bb);
						dominated_by_p(CDI_DOMINATORS,free_t->bb,free_t->fun->cfg->x_exit_block_ptr->prev_bb);
						if (dominated_by_p(CDI_DOMINATORS,free_t->bb,free_t->fun->cfg->x_exit_block_ptr->prev_bb) ^ dominated_by_p(CDI_DOMINATORS,free2_t->bb,free2_t->fun->cfg->x_exit_block_ptr->prev_bb)){
							errorm=POINTER_MAY;
						}
						else if (dominated_by_p(CDI_DOMINATORS,free_t->bb,free_t->fun->cfg->x_exit_block_ptr->prev_bb) && dominated_by_p(CDI_DOMINATORS,free2_t->bb,free2_t->fun->cfg->x_exit_block_ptr->prev_bb)){
							errorm=POINTER_MUST;
						}
						else if (!dominated_by_p(CDI_DOMINATORS,free_t->bb,free_t->fun->cfg->x_exit_block_ptr->prev_bb) && !dominated_by_p(CDI_DOMINATORS,free2_t->bb,free2_t->fun->cfg->x_exit_block_ptr->prev_bb)){
							if(fDFS->get(free_t->node)->is_succ(free_t->bb,free2_t->bb) || fDFS->get(free2_t->node)->is_succ(free2_t->bb,free_t->bb)){
								errorm=POINTER_MAY;
							}
						}
						int phicount=0;
						/*algorithm 9*/
						if(fDFS->get(free_t->node)->is_succ(free_t->bb,free2_t->bb)){
							if(gimple_code (free2_t->last_stmt) == GIMPLE_PHI){
								for(unsigned i=0;i<gimple_phi_num_args(free2_t->last_stmt);i++){

									tree argu=gimple_phi_arg_def(free2_t->last_stmt,i);
									gphi *phi=as_a <gphi *> (free2_t->last_stmt);
									basic_block src = gimple_phi_arg_edge (phi, i)->src;
									
									//fprintf(stderr,"phi_argu:%d ",i);
									//debug_tree(argu);
									pi2=get_ptr_info (argu);
									pt2=&pi2->pt;
									if(pt2->vars==NULL)
										continue;
									if(bitmap_intersect_p(pt->vars,pt2->vars)){
										if(fDFS->get(free_t->node)->is_succ(free_t->bb,src)){
											errorm=POINTER_MAY;
											phicount++;
										}
									}
								}
							}						
						}else if(fDFS->get(free_t->node)->is_succ(free2_t->bb,free_t->bb)){
							if(gimple_code (free_t->last_stmt) == GIMPLE_PHI){
								for(unsigned i=0;i<gimple_phi_num_args(free_t->last_stmt);i++){

									tree argu=gimple_phi_arg_def(free_t->last_stmt,i);
									gphi *phi=as_a <gphi *> (free_t->last_stmt);
									basic_block src = gimple_phi_arg_edge (phi, i)->src;
									
									//fprintf(stderr,"phi_argu:%d ",i);
									//debug_tree(argu);
									pi2=get_ptr_info (argu);
									pt2=&pi2->pt;
									if(pt2->vars==NULL)
										continue;
									if(bitmap_intersect_p(pt->vars,pt2->vars)){
										if(fDFS->get(free_t->node)->is_succ(free2_t->bb,src)){
											errorm=POINTER_MAY;
											phicount++;
										}
									}
								}
							}	
						}
						if(phicount!=0)
							errorm=POINTER_NOT;
						free_dominance_info (CDI_DOMINATORS);
						pop_cfun();
						//fprintf(stderr,"		=======search ptable %d %d========\n",free_t->fun,free2_t->fun);
						
						if(ipa){
							/*algorithm 11*/
							FOR_EACH_TABLE(malloc_t,t3){
								if(ptr_derefs_may_alias_p(free_t->target,malloc_t->target)){
									if(free_t->node!=malloc_t->node){
										
										//fprintf(stderr,"			=======free:");
										//debug_head(free_t->target);
										//fprintf(stderr,"			=======malloc:");
										//debug_head(malloc_t->target);
										//fprintf(stderr,"			=======search_all_path ========\n");
										search_all_path(free_t,malloc_t);
										//fprintf(stderr,"			=======print_tvpt %d========\n",free_t->target);
										//debug_head(free_t->target);
										print_tvpt(free_t->target);
										//fprintf(stderr,"			=======print_tvpt %d========\n",free2_t->target);
										//debug_head(free2_t->target);
										print_tvpt(free2_t->target);
										if(!same_path(free_t->target,free2_t->target))
											errorm=POINTER_NOT;  //problem
										}
								}
							}
						}
						malloc_t=ptable;
						//fprintf(stderr,"		=======search ptable end %d========\n",errorm);
						
						
						//fprintf(stderr,"	=======search ftable2 end========\n");
					}
					else{
						if(ipa){
							/*algorithm 10*/
							//if(from_different_function(free_t,free2_t))
								//errorm=POINTER_MAY;
						}
					}
					switch(errorm){
						case POINTER_MUST:
							warning_at(free_t->loc,0,"Double free error!");
							warning_at(free2_t->loc,0,"");
							fprintf(stderr,"%s \n",get_name(free_t->node->decl));
							fprintf(stderr,"%s \n",get_name(free2_t->node->decl));
							//fprintf(fp,"%s Double-free must\n",DECL_SOURCE_FILE (main_fun->decl));
							
							must++;
							break;
						case POINTER_MAY:
							warning_at(free_t->loc,0,"May Double free error!");
							warning_at(free2_t->loc,0,"");
							
							fprintf(stderr,"%s \n",get_name(free_t->node->decl));
							fprintf(stderr,"%s \n",get_name(free2_t->node->decl));
							//fprintf(fp,"%s Double-free may\n",DECL_SOURCE_FILE (main_fun->decl));
							may++;
							break;
						default:						
							break;
					}
					FOR_EACH_TABLE(malloc_t,t3){
						pi2= SSA_NAME_PTR_INFO (malloc_t->target);
						pt2=&pi2->pt;
						if(bitmap_intersect_p(pt->vars,pt2->vars)){
							//warning_at(malloc_t->loc,0,"malloc location \n");
						}
					}
					malloc_t=ptable;
				/*
				fprintf(stderr,"\n%d:%d\n",free_t->bb->index,free2_t->bb->index);
				warning_at(free_t->loc,0,"loc: %d",free_t->bb->index);
				warning_at(free2_t->loc,0,"loc: %d",free2_t->bb->index);
				if (dominated_by_p(CDI_DOMINATORS,free2_t->bb,free_t->bb)){
					if()
					warning_at(free_t->loc,0,"Double-free %d",free_t->bb->index);
					warning_at(free2_t->loc,0,"Double-free %d",free2_t->bb->index);
					debug_head(free_t->target);
					struct pt_solution *pt=&pi1->pt;
					//debug(&pi1->pt);
					FILE *file;
					dump_decl_set (stderr,pt->vars);
					fprintf(stderr,"\n");
					debug_head(free2_t->target);
					debug(&pi2->pt);
					fprintf(stderr,"\n");
					if(pt_solutions_intersect (&pi1->pt,&pi2->pt)){
						
						gimple_array *used_stmt;
						gimple_array gstart;
	      					gstart.stmt = NULL;
	      					used_stmt = &gstart;
	      					//search_ptr_use(used_stmt, free_t->target);
						fprintf(stderr,"~.~\n");
	      					//search_ptr_use(used_stmt, free2_t->target);
					}
					fprintf(stderr,"----------------\n");
					break;
				}
				if(et_below(n2,n1)){
					warning_at(free_t->loc,0,"May Double-free %d",free_t->bb->index);
					warning_at(free2_t->loc,0,"May Double-free %d",free2_t->bb->index);
				}
				if(g.is_succ(free_t->bb,free2_t->bb)){
					warning_at(free_t->loc,0,"May Double-free %d",free_t->bb->index);
					warning_at(free2_t->loc,0,"May Double-free %d",free2_t->bb->index);
				}
				*/
			}
    	}
	}
	if(main_fun!=NULL){
		//fprintf(fp,"%s Memory Leak Error \n",DECL_SOURCE_FILE (table1->fun->decl));
		//fprintf(fp,"%s Double free Error \n		Total free:%d\n		May df:%d\n		Must df:%d\n",DECL_SOURCE_FILE (main_fun->decl),total,may,must);
	}else{
		//fprintf(fp,"Double free Error \n		Total free:%d\n		May df:%d\n		Must df:%d\n",total,may,must);
	}
}

void collect_malloc(gimple *gc,cgraph_node *node,basic_block bb){
	location_t loc = gimple_location(gc);
	tree a;
	cgraph_node* node2;
	const char *name;

	if(gimple_call_fn(gc)==NULL)
		return;

	name=get_name(gimple_call_fn(gc));
	if (!strcmp(name,"free") || !strcmp(name,"xfree"))
	{
		set_ptb(bb, ftable, gimple_call_arg(gc, 0), loc, 0, gc,node);
	}
	else if(!strcmp(name,"malloc") || !strcmp(get_name(gimple_call_fn(gc)),"calloc")|| !strcmp(name,"xmalloc")|| !strcmp(name,"strdup"))
	{		
		set_ptb(bb, ptable, gimple_call_lhs(gc), loc, 0, gc,node);
	}
	a=gimple_call_fn(gc);
	fnode->put(a,node);
	
	var_points_to vpt;
	vector<vector<pair<fdecl,location_t>>> may_malloc_path;
	vpt.may_malloc_path=may_malloc_path;
	tvpt->put(gimple_call_lhs (gc),vpt);
}

void print_pointer_table_new(ptb *ptable){
	ptb *temp1=ptable;
	while(temp1->target!=NULL_TREE ){
		if(get_name(temp1->target)!=NULL){
			debug_head(temp1->target);
			warning_at(temp1->loc,0, "%s", get_name(temp1->target));
			struct ptr_info_def *pi=SSA_NAME_PTR_INFO (temp1->target);
			struct pt_solution *pt=&pi->pt;
			debug(pt);
			
			fprintf(stderr,"address:%d \n",temp1->target);
		}
		else {
			debug_head(temp1->target);
			warning_at(temp1->loc,0, "NULL");
			struct ptr_info_def *pi=SSA_NAME_PTR_INFO (temp1->target);
			struct pt_solution *pt=&pi->pt;
			debug(pt);
			fprintf(stderr,"address:%d \n",temp1->target);
		}
		if(temp1->next!=NULL)
			temp1=temp1->next;
		else break;
	}
}
void detect(){
	struct cgraph_node *node;
	struct var_points_to vpt;
	tree ptr;
	unsigned i;
	function *ofun;
	function *fn;
	basic_block bb;
	ipa=true;
	tvpt = new hash_map<tree,var_points_to >;
	fDFS = new hash_map<cgraph_node *, Graph >;
	fnode= new hash_map<tree, cgraph_node *>;
	//fprintf(stderr,"=======ipa_pta=========\n");
	/*initialization table*/
	init_table();
	FOR_EACH_DEFINED_FUNCTION (node)
	{
		if(!ipa)
			init_table();
		push_cfun(node->get_fun());
		if (cfun==NULL)
			continue;
		if(strcmp(get_name(cfun->decl),"main")==0){
			main_fun=cfun;
			main_node=node;
		}
		//fprintf(stderr,"=======node_fun:%s=========\n",get_name(cfun->decl));

		/*initialization DFS graph*/
		Graph DFS;
		DFS.init_Graph(cfun->cfg->x_last_basic_block);
		/*calculate dominator tree*/
		calculate_dominance_info(CDI_DOMINATORS);

		/*create DFS graph, Algorithm 1 and 2*/
		FOR_EACH_BB_FN (bb, cfun){			
			if(bb != cfun->cfg->x_exit_block_ptr->prev_bb){
				edge e;
				edge_iterator ei;
				//fprintf(stderr,"node:= %d \n succs:=",bb->index);
				FOR_EACH_EDGE (e, ei, bb->succs)
				{
					DFS.addEdge(bb->index,e->dest->index);
					//fprintf(stderr,"%d",e->dest->index);
				}
			}
			for (gimple_stmt_iterator gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
			{
				gimple *gc = gsi_stmt (gsi);
				//debug_gimple_stmt(gc);
				if (is_gimple_call(gc)){
					/*collect malloc and free information*/
					collect_malloc(gc,node,bb);		
				}
			}
		}
		/*DFS of this function put set "fDfS" */
		fDFS->put(node,DFS);
		if(!ipa){
			new_memory_leak_analysis (ptable,ftable);
			new_double_free_analysis(ptable,ftable);
			new_use_after_free_analysis(ptable, ftable);
		}		
		pop_cfun();
	}
	
	if(ipa){
		new_memory_leak_analysis (ptable,ftable);
		new_double_free_analysis(ptable,ftable);
		new_use_after_free_analysis(ptable, ftable);
	}	
}
void insert_always_inline(){
	cgraph_node* node;
	const char *name;
	bool always_inline;
	//fprintf(stderr,"=======inline=========\n");
	FOR_EACH_DEFINED_FUNCTION (node)
	{
		basic_block bb;
		cgraph_edge* e;
		
		//fprintf(stderr,"=======node_fun:%s %d=========\n",get_name(node->decl),node->decl);
		//fprintf(stderr,"attribute:%s \n",IDENTIFIER_POINTER (node->decl));

		//fprintf(stderr,"attribute:%s \n",IDENTIFIER_POINTER (DECL_ASSEMBLER_NAME (node->decl)));
		//node->debug();
		//fprintf(stderr,"=======fun:%d=========\n",get_name(node->decl));
		tree attr ;
		enum availability avail;
		for (e = node->callees; e; e = e->next_callee)
		{
			cgraph_node *caller = e->caller->global.inlined_to ? e->caller->global.inlined_to : e->caller;
			cgraph_node *callee = e->callee->ultimate_alias_target (&avail, caller);
			tree callee_tree = callee ? DECL_FUNCTION_SPECIFIC_OPTIMIZATION (callee->decl) : NULL;
			//DECL_DISREGARD_INLINE_LIMITS (callee->decl)=1;
			if (DECL_ATTRIBUTES (callee->decl)!=NULL){
				attr = get_attribute_name (DECL_ATTRIBUTES (callee->decl));
				//debug_tree(attr);
			}else{
				//if(callee->decl)
				//DECL_ATTRIBUTES (callee->decl) = tree_cons (get_identifier ("always_inline"),
                                //NULL, DECL_ATTRIBUTES (callee->decl));
			}
			always_inline =(DECL_DISREGARD_INLINE_LIMITS (callee->decl)
              && lookup_attribute ("always_inline", DECL_ATTRIBUTES (callee->decl)));
			//fprintf(stderr,"=======%s 's address:%d %d=========\n",get_name(callee->decl),callee->decl,always_inline);
		}
		
		
		//node->debug();
		push_cfun(DECL_STRUCT_FUNCTION (node->decl));
		if(cfun==NULL){
			fprintf(stderr,"=======NULL=========\n");
		}
		FOR_EACH_BB_FN (bb, cfun){
			
			for (gimple_stmt_iterator gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
			{
				gimple *gc = gsi_stmt (gsi);
				//debug_gimple_stmt(gc);
				if (is_gimple_call(gc)){

					if(gimple_call_fn(gc)==NULL)
						continue;
					name= get_name (gimple_call_fn(gc));
					if(name==NULL)
						continue;
					//fprintf(stderr, "functionname %s\n",name);
					if(!strcmp(name,"free") ||
						!strcmp(name,"xfree") ||
						!strcmp(name,"malloc") || 
						!strcmp(name,"xmalloc")||
						!strcmp(name,"calloc")||
						!strcmp(name,"xcalloc")||
						!strcmp(name,"strdup") ){
					
						//fprintf(stderr,"=======add_always:%d=========\n",node->decl);
						always_inline =(DECL_DISREGARD_INLINE_LIMITS (node->decl)
		          && lookup_attribute ("always_inline", DECL_ATTRIBUTES (node->decl)));
						if(!always_inline && !MAIN_NAME_P (DECL_NAME (node->decl))){
							DECL_ATTRIBUTES (node->decl) = tree_cons (get_identifier ("always_inline"),NULL, DECL_ATTRIBUTES (node->decl));
							DECL_DISREGARD_INLINE_LIMITS (node->decl)=1;
							//printf("always_inline\n");
						}
					}
					
				}
			
			}
		}
		pop_cfun();
	}

}
