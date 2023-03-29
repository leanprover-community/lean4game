// Lean compiler output
// Module: NNG.Modifications.Tactics
// Imports: Init Mathlib.Lean.Expr.Basic NNG.MyNat.Addition Lean.Elab.Tactic.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Meta_getElimInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MyNat_induction;
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
static lean_object* l_MyNat_induction___closed__14;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__7;
lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_MyNat_rfl___closed__4;
extern lean_object* l_Lean_Parser_Tactic_location;
static lean_object* l_MyNat_induction___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_ElimApp_evalNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MyNat_evalRfl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Elab_Tactic_closeMainGoal___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_MyNat_induction___closed__11;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l_MyNat_rewriteSeq___closed__10;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_casesTarget;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MyNat_induction___closed__24;
lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Tactic_ElimApp_evalNames___closed__1;
LEAN_EXPORT lean_object* l_MyNat_evalRfl(lean_object*);
static lean_object* l_MyNat_rewriteSeq___closed__7;
static lean_object* l_MyNat_rewriteSeq___closed__5;
static lean_object* l_MyNat_induction___closed__12;
lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Std_Tactic___aux__Std__Tactic__ShowTerm______elabRules__Std__Tactic__showTermTac__1___spec__1___rarg(lean_object*);
lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MyNat_rewriteSeq___closed__12;
static lean_object* l_MyNat_evalRewriteSeq___lambda__2___closed__1;
lean_object* l_Lean_Elab_Tactic_ElimApp_mkElimApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27(lean_object*);
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MyNat_rewriteSeq___closed__15;
static lean_object* l_MyNat_induction___closed__17;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___lambda__1___boxed(lean_object**);
static lean_object* l_MyNat_rewriteSeq___closed__11;
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l_MyNat_rewriteSeq___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__4;
static lean_object* l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___lambda__1___closed__1;
static lean_object* l_MyNat_induction___closed__8;
static lean_object* l_MyNat_evalRewriteSeq___lambda__2___closed__4;
extern lean_object* l_Lean_Parser_Tactic_rwRuleSeq;
lean_object* l_Lean_Elab_Tactic_elabCasesTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MyNat_evalRewriteSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__6;
LEAN_EXPORT lean_object* l_MyNat_evalRewriteSeq___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MyNat_induction___closed__20;
static lean_object* l_MyNat_induction___closed__9;
LEAN_EXPORT lean_object* l_MyNat_evalRfl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MyNat_evalRewriteSeq___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_addImplicitTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MyNat_rfl___closed__2;
static lean_object* l_MyNat_induction___closed__15;
static lean_object* l_MyNat_rewriteSeq___closed__6;
lean_object* l_Lean_Expr_addLocalVarInfoForBinderIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
static lean_object* l_MyNat_induction___closed__16;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MyNat_evalRewriteSeq___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MyNat_induction___closed__22;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__1;
static lean_object* l_MyNat_rfl___closed__1;
LEAN_EXPORT lean_object* l_MyNat_evalRewriteSeq___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MyNat_induction___closed__3;
static lean_object* l_MyNat_evalRfl___rarg___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__2;
LEAN_EXPORT lean_object* l_MyNat_evalRewriteSeq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__5;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MyNat_rewriteSeq___closed__14;
static lean_object* l_MyNat_induction___closed__10;
static lean_object* l_MyNat_rewriteSeq___closed__9;
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MyNat_induction___closed__1;
static lean_object* l_MyNat_rewriteSeq___closed__2;
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__8;
static lean_object* l_MyNat_evalRewriteSeq___lambda__2___closed__5;
static lean_object* l_MyNat_induction___closed__5;
static lean_object* l_MyNat_rewriteSeq___closed__4;
static lean_object* l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___closed__2;
LEAN_EXPORT lean_object* l_MyNat_evalRewriteSeq___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_MyNat_evalRewriteSeq___lambda__3___closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_MyNat_rfl___closed__3;
static lean_object* l_MyNat_induction___closed__21;
lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_binderIdent;
lean_object* l_Lean_RBTree_toArray___at_Lean_Meta_getFVarsToGeneralize___spec__1(lean_object*);
static lean_object* l_MyNat_induction___closed__4;
static lean_object* l_MyNat_induction___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MyNat_induction___closed__23;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_ElimApp_evalNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabRewriteConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_splitAtD___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_MyNat_rewriteSeq___closed__3;
LEAN_EXPORT lean_object* l_MyNat_rfl;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MyNat_rewriteSeq___closed__13;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
static lean_object* l_MyNat_induction___closed__19;
LEAN_EXPORT lean_object* l_MyNat_evalRewriteSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MyNat_rewriteSeq___closed__8;
extern lean_object* l_Lean_Parser_Tactic_config;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__9;
lean_object* l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MyNat_evalRfl___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_sortFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalInduction_checkTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalInduction___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_MyNat_rewriteSeq;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_MyNat_induction___closed__6;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MyNat_induction___closed__18;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_MyNat_evalRewriteSeq___lambda__2___closed__3;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_ElimApp_setMotiveArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MyNat_evalRewriteSeq___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_MyNat_induction___closed__13;
static lean_object* _init_l_MyNat_rewriteSeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("MyNat", 5);
return x_1;
}
}
static lean_object* _init_l_MyNat_rewriteSeq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rewriteSeq", 10);
return x_1;
}
}
static lean_object* _init_l_MyNat_rewriteSeq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_MyNat_rewriteSeq___closed__1;
x_2 = l_MyNat_rewriteSeq___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_MyNat_rewriteSeq___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_MyNat_rewriteSeq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_MyNat_rewriteSeq___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_MyNat_rewriteSeq___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rw", 2);
return x_1;
}
}
static lean_object* _init_l_MyNat_rewriteSeq___closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_MyNat_rewriteSeq___closed__6;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_MyNat_rewriteSeq___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("optional", 8);
return x_1;
}
}
static lean_object* _init_l_MyNat_rewriteSeq___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_MyNat_rewriteSeq___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_MyNat_rewriteSeq___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_MyNat_rewriteSeq___closed__9;
x_2 = l_Lean_Parser_Tactic_config;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_MyNat_rewriteSeq___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_MyNat_rewriteSeq___closed__5;
x_2 = l_MyNat_rewriteSeq___closed__7;
x_3 = l_MyNat_rewriteSeq___closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_MyNat_rewriteSeq___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_MyNat_rewriteSeq___closed__5;
x_2 = l_MyNat_rewriteSeq___closed__11;
x_3 = l_Lean_Parser_Tactic_rwRuleSeq;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_MyNat_rewriteSeq___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_MyNat_rewriteSeq___closed__9;
x_2 = l_Lean_Parser_Tactic_location;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_MyNat_rewriteSeq___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_MyNat_rewriteSeq___closed__5;
x_2 = l_MyNat_rewriteSeq___closed__12;
x_3 = l_MyNat_rewriteSeq___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_MyNat_rewriteSeq___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_MyNat_rewriteSeq___closed__3;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_MyNat_rewriteSeq___closed__14;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_MyNat_rewriteSeq() {
_start:
{
lean_object* x_1; 
x_1 = l_MyNat_rewriteSeq___closed__15;
return x_1;
}
}
LEAN_EXPORT lean_object* l_MyNat_evalRewriteSeq___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_rewriteLocalDecl(x_1, x_2, x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
static lean_object* _init_l_MyNat_evalRewriteSeq___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rewrite", 7);
return x_1;
}
}
static lean_object* _init_l_MyNat_evalRewriteSeq___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_MyNat_evalRewriteSeq___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_MyNat_evalRewriteSeq___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("did not find instance of the pattern in the current goal", 56);
return x_1;
}
}
static lean_object* _init_l_MyNat_evalRewriteSeq___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_MyNat_evalRewriteSeq___lambda__2___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_MyNat_evalRewriteSeq___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_MyNat_evalRewriteSeq___lambda__2___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MyNat_evalRewriteSeq___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_MyNat_evalRewriteSeq___lambda__2___closed__2;
x_12 = l_MyNat_evalRewriteSeq___lambda__2___closed__5;
x_13 = l_Lean_Meta_throwTacticEx___rarg(x_11, x_1, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_MyNat_evalRewriteSeq___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_MyNat_evalRewriteSeq___lambda__2___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MyNat_evalRewriteSeq___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_box(x_3);
lean_inc(x_1);
lean_inc(x_4);
x_15 = lean_alloc_closure((void*)(l_MyNat_evalRewriteSeq___lambda__1___boxed), 13, 3);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_1);
x_16 = lean_box(x_3);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___boxed), 12, 3);
lean_closure_set(x_17, 0, x_4);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_1);
x_18 = l_MyNat_evalRewriteSeq___lambda__3___closed__1;
x_19 = l_Lean_Elab_Tactic_withLocation(x_2, x_15, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
}
LEAN_EXPORT lean_object* l_MyNat_evalRewriteSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_Tactic_elabRewriteConfig(x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Elab_Tactic_expandOptLocation(x_17);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = lean_alloc_closure((void*)(l_MyNat_evalRewriteSeq___lambda__3___boxed), 13, 2);
lean_closure_set(x_23, 0, x_14);
lean_closure_set(x_23, 1, x_18);
x_24 = l_Lean_Elab_Tactic_withRWRulesSeq(x_20, x_22, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_MyNat_evalRewriteSeq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_MyNat_evalRewriteSeq___lambda__1(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_MyNat_evalRewriteSeq___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_MyNat_evalRewriteSeq___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_MyNat_evalRewriteSeq___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_MyNat_evalRewriteSeq___lambda__3(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_MyNat_evalRewriteSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_MyNat_evalRewriteSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_getArg(x_5, x_7);
lean_dec(x_5);
x_9 = l_Lean_Elab_Tactic_getNameOfIdent_x27(x_8);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_9);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_11, x_13);
lean_dec(x_11);
x_15 = l_Lean_Elab_Tactic_getNameOfIdent_x27(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
x_1 = x_12;
x_2 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_17; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_dec(x_6);
x_20 = l_Lean_Expr_fvar___override(x_16);
x_21 = l_Lean_Meta_FVarSubst_apply(x_1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Expr_addLocalVarInfoForBinderIdent), 9, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_23 = l_Lean_MVarId_withContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_2, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 1;
x_26 = lean_usize_add(x_5, x_25);
x_5 = x_26;
x_6 = x_19;
x_13 = x_24;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_MVarId_tryClear(x_4, x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_13;
x_9 = x_14;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_9);
return x_22;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = l_Lean_SourceInfo_fromRef(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hole", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__2;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__3;
x_3 = l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__4;
x_4 = l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__7;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__6;
x_3 = l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__8;
x_4 = l_Lean_Syntax_node1(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_7, x_6);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_array_uget(x_5, x_7);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 2);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_30 = x_8;
} else {
 lean_dec_ref(x_8);
 x_30 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_31 = l___private_Lean_Elab_Tactic_Induction_0__Lean_Elab_Tactic_ElimApp_getAltNumFields(x_1, x_26, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__9;
lean_inc(x_32);
x_35 = l_List_splitAtD___rarg(x_32, x_28, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_box(0);
lean_inc(x_36);
x_39 = l_List_mapTR_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__1(x_36, x_38);
x_40 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_41 = l_Lean_Meta_introNCore(x_27, x_32, x_39, x_40, x_40, x_11, x_12, x_13, x_14, x_33);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_box(0);
x_47 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_2);
x_48 = l_Lean_Meta_Cases_unifyEqs_x3f(x_2, x_45, x_46, x_47, x_11, x_12, x_13, x_14, x_43);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_44);
lean_dec(x_36);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
if (lean_is_scalar(x_30)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_30;
}
lean_ctor_set(x_51, 0, x_37);
lean_ctor_set(x_51, 1, x_29);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_19 = x_52;
x_20 = x_50;
goto block_25;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_72; lean_object* x_73; 
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_72 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_3);
x_73 = l_Lean_Meta_introNCore(x_55, x_3, x_38, x_40, x_72, x_11, x_12, x_13, x_14, x_54);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_array_get_size(x_4);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_lt(x_78, x_77);
if (x_79 == 0)
{
lean_dec(x_77);
x_57 = x_76;
x_58 = x_75;
goto block_71;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_77, x_77);
if (x_80 == 0)
{
lean_dec(x_77);
x_57 = x_76;
x_58 = x_75;
goto block_71;
}
else
{
size_t x_81; size_t x_82; lean_object* x_83; 
x_81 = 0;
x_82 = lean_usize_of_nat(x_77);
lean_dec(x_77);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_83 = l_Array_foldlMUnsafe_fold___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__3(x_4, x_81, x_82, x_76, x_11, x_12, x_13, x_14, x_75);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_57 = x_84;
x_58 = x_85;
goto block_71;
}
else
{
uint8_t x_86; 
lean_dec(x_56);
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
return x_83;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_83, 0);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_83);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_56);
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_73);
if (x_90 == 0)
{
return x_73;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_73, 0);
x_92 = lean_ctor_get(x_73, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_73);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
block_71:
{
lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; 
x_59 = lean_array_get_size(x_44);
x_60 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_61 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_57);
x_62 = l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__2(x_56, x_57, x_44, x_60, x_61, x_36, x_9, x_10, x_11, x_12, x_13, x_14, x_58);
lean_dec(x_44);
lean_dec(x_56);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_array_push(x_29, x_57);
if (lean_is_scalar(x_30)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_30;
}
lean_ctor_set(x_65, 0, x_37);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_19 = x_66;
x_20 = x_63;
goto block_25;
}
else
{
uint8_t x_67; 
lean_dec(x_57);
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_62);
if (x_67 == 0)
{
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_62, 0);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_62);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_48);
if (x_94 == 0)
{
return x_48;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_48, 0);
x_96 = lean_ctor_get(x_48, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_48);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_41);
if (x_98 == 0)
{
return x_41;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_41, 0);
x_100 = lean_ctor_get(x_41, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_41);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_31);
if (x_102 == 0)
{
return x_31;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_31, 0);
x_104 = lean_ctor_get(x_31, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_31);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
block_25:
{
lean_object* x_21; size_t x_22; size_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_7, x_22);
x_7 = x_23;
x_8 = x_21;
x_15 = x_20;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Parser_Tactic_ElimApp_evalNames___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_ElimApp_evalNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_3, x_14);
x_16 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_17 = lean_array_to_list(lean_box(0), x_16);
x_18 = l_Lean_Parser_Tactic_ElimApp_evalNames___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_get_size(x_2);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
x_23 = l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4(x_1, x_4, x_5, x_6, x_2, x_21, x_22, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__2(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4(x_1, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_ElimApp_evalNames___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Parser_Tactic_ElimApp_evalNames(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l_MyNat_induction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_MyNat_induction___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_root_", 6);
return x_1;
}
}
static lean_object* _init_l_MyNat_induction___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("induction", 9);
return x_1;
}
}
static lean_object* _init_l_MyNat_induction___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__2;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__3;
x_3 = l_MyNat_induction___closed__1;
x_4 = l_MyNat_induction___closed__2;
x_5 = l_MyNat_rewriteSeq___closed__1;
x_6 = l_MyNat_induction___closed__3;
x_7 = l_Lean_Name_mkStr6(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_MyNat_induction___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("induction ", 10);
return x_1;
}
}
static lean_object* _init_l_MyNat_induction___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_MyNat_induction___closed__5;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_MyNat_induction___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", ", 2);
return x_1;
}
}
static lean_object* _init_l_MyNat_induction___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_MyNat_induction___closed__7;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_MyNat_induction___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_MyNat_induction___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_casesTarget;
x_2 = l_MyNat_induction___closed__9;
x_3 = l_MyNat_induction___closed__8;
x_4 = 0;
x_5 = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_MyNat_induction___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_MyNat_rewriteSeq___closed__5;
x_2 = l_MyNat_induction___closed__6;
x_3 = l_MyNat_induction___closed__10;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_MyNat_induction___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" with ", 6);
return x_1;
}
}
static lean_object* _init_l_MyNat_induction___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_MyNat_induction___closed__12;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_MyNat_induction___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("many1", 5);
return x_1;
}
}
static lean_object* _init_l_MyNat_induction___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_MyNat_induction___closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_MyNat_induction___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("colGt", 5);
return x_1;
}
}
static lean_object* _init_l_MyNat_induction___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_MyNat_induction___closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_MyNat_induction___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_MyNat_induction___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_MyNat_induction___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_MyNat_rewriteSeq___closed__5;
x_2 = l_MyNat_induction___closed__18;
x_3 = l_Lean_binderIdent;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_MyNat_induction___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_MyNat_induction___closed__15;
x_2 = l_MyNat_induction___closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_MyNat_induction___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_MyNat_rewriteSeq___closed__5;
x_2 = l_MyNat_induction___closed__13;
x_3 = l_MyNat_induction___closed__20;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_MyNat_induction___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_MyNat_rewriteSeq___closed__9;
x_2 = l_MyNat_induction___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_MyNat_induction___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_MyNat_rewriteSeq___closed__5;
x_2 = l_MyNat_induction___closed__11;
x_3 = l_MyNat_induction___closed__22;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_MyNat_induction___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_MyNat_induction___closed__4;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_MyNat_induction___closed__23;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_MyNat_induction() {
_start:
{
lean_object* x_1; 
x_1 = l_MyNat_induction___closed__24;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_18 = l_Lean_Meta_mkGeneralizationForbiddenSet(x_1, x_2, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 0;
lean_inc(x_13);
x_22 = l_Lean_Meta_getFVarSetToGeneralize(x_1, x_19, x_21, x_13, x_14, x_15, x_16, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_RBTree_toArray___at_Lean_Meta_getFVarsToGeneralize___spec__1(x_23);
lean_inc(x_13);
x_26 = l_Lean_Meta_sortFVarIds(x_25, x_13, x_14, x_15, x_16, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_29 = l_Lean_MVarId_revert(x_3, x_27, x_21, x_21, x_13, x_14, x_15, x_16, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
lean_inc(x_33);
x_34 = l_Lean_MVarId_getTag(x_33, x_13, x_14, x_15, x_16, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_15, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_15, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_15, 4);
lean_inc(x_41);
x_42 = lean_ctor_get(x_15, 5);
lean_inc(x_42);
x_43 = lean_ctor_get(x_15, 6);
lean_inc(x_43);
x_44 = lean_ctor_get(x_15, 7);
lean_inc(x_44);
x_45 = lean_ctor_get(x_15, 8);
lean_inc(x_45);
x_46 = lean_ctor_get(x_15, 9);
lean_inc(x_46);
x_47 = lean_ctor_get(x_15, 10);
lean_inc(x_47);
x_48 = l_Lean_replaceRef(x_4, x_42);
lean_dec(x_42);
x_49 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_49, 0, x_37);
lean_ctor_set(x_49, 1, x_38);
lean_ctor_set(x_49, 2, x_39);
lean_ctor_set(x_49, 3, x_40);
lean_ctor_set(x_49, 4, x_41);
lean_ctor_set(x_49, 5, x_48);
lean_ctor_set(x_49, 6, x_43);
lean_ctor_set(x_49, 7, x_44);
lean_ctor_set(x_49, 8, x_45);
lean_ctor_set(x_49, 9, x_46);
lean_ctor_set(x_49, 10, x_47);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
x_50 = l_Lean_Elab_Tactic_ElimApp_mkElimApp(x_5, x_1, x_35, x_11, x_12, x_13, x_14, x_49, x_16, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_80 = lean_unsigned_to_nat(0u);
x_81 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_53, x_80);
x_82 = l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___lambda__1___closed__1;
lean_inc(x_81);
x_83 = lean_mk_array(x_81, x_82);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_sub(x_81, x_84);
lean_dec(x_81);
lean_inc(x_53);
x_86 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_53, x_83, x_85);
x_87 = lean_ctor_get(x_5, 1);
lean_inc(x_87);
x_88 = lean_array_get_size(x_86);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_87);
lean_dec(x_86);
x_90 = l_Lean_instInhabitedExpr;
x_91 = l___private_Init_Util_0__outOfBounds___rarg(x_90);
x_54 = x_91;
goto block_79;
}
else
{
lean_object* x_92; 
x_92 = lean_array_fget(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
x_54 = x_92;
goto block_79;
}
block_79:
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Lean_Expr_mvarId_x21(x_54);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_6);
lean_inc(x_33);
x_56 = l_Lean_Elab_Tactic_ElimApp_setMotiveArg(x_33, x_55, x_6, x_13, x_14, x_15, x_16, x_52);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Lean_MVarId_assign___at_Lean_Elab_Tactic_closeMainGoal___spec__1(x_33, x_53, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_57);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
x_61 = lean_array_get_size(x_32);
lean_dec(x_32);
x_62 = lean_unsigned_to_nat(0u);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_63 = l_Lean_Parser_Tactic_ElimApp_evalNames(x_5, x_60, x_7, x_62, x_61, x_6, x_11, x_12, x_13, x_14, x_15, x_16, x_59);
lean_dec(x_6);
lean_dec(x_60);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_51, 2);
lean_inc(x_66);
lean_dec(x_51);
x_67 = l_Array_append___rarg(x_64, x_66);
x_68 = lean_array_to_list(lean_box(0), x_67);
x_69 = l_List_appendTR___rarg(x_68, x_8);
x_70 = l_Lean_Elab_Tactic_setGoals(x_69, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_65);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_70;
}
else
{
uint8_t x_71; 
lean_dec(x_51);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_71 = !lean_is_exclusive(x_63);
if (x_71 == 0)
{
return x_63;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_63, 0);
x_73 = lean_ctor_get(x_63, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_63);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_75 = !lean_is_exclusive(x_56);
if (x_75 == 0)
{
return x_56;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_56, 0);
x_77 = lean_ctor_get(x_56, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_56);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_93 = !lean_is_exclusive(x_50);
if (x_93 == 0)
{
return x_50;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_50, 0);
x_95 = lean_ctor_get(x_50, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_50);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_34);
if (x_97 == 0)
{
return x_34;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_34, 0);
x_99 = lean_ctor_get(x_34, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_34);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_29);
if (x_101 == 0)
{
return x_29;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_29, 0);
x_103 = lean_ctor_get(x_29, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_29);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_18);
if (x_105 == 0)
{
return x_18;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_18, 0);
x_107 = lean_ctor_get(x_18, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_18);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_17 = l_Lean_Meta_getElimInfo(x_1, x_2, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_18);
x_20 = l_Lean_Meta_addImplicitTargets(x_18, x_3, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Tactic_evalInduction_checkTargets(x_21, x_12, x_13, x_14, x_15, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_array_get_size(x_21);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
lean_inc(x_21);
x_28 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalInduction___spec__2(x_26, x_27, x_21);
x_29 = lean_box(0);
lean_inc(x_4);
x_30 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___lambda__1___boxed), 17, 8);
lean_closure_set(x_30, 0, x_21);
lean_closure_set(x_30, 1, x_29);
lean_closure_set(x_30, 2, x_4);
lean_closure_set(x_30, 3, x_5);
lean_closure_set(x_30, 4, x_18);
lean_closure_set(x_30, 5, x_28);
lean_closure_set(x_30, 6, x_6);
lean_closure_set(x_30, 7, x_7);
x_31 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_4, x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_24);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_23);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
return x_20;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_20);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_17);
if (x_40 == 0)
{
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_17);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rec'", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_MyNat_rewriteSeq___closed__1;
x_2 = l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_MyNat_induction___closed__4;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Std_Tactic___aux__Std__Tactic__ShowTerm______elabRules__Std__Tactic__showTermTac__1___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
x_18 = l_Lean_Syntax_getSepArgs(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Elab_Tactic_elabCasesTargets(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_15);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_box(0);
x_30 = l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___closed__2;
lean_inc(x_27);
x_31 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___lambda__2), 16, 7);
lean_closure_set(x_31, 0, x_30);
lean_closure_set(x_31, 1, x_29);
lean_closure_set(x_31, 2, x_20);
lean_closure_set(x_31, 3, x_27);
lean_closure_set(x_31, 4, x_15);
lean_closure_set(x_31, 5, x_17);
lean_closure_set(x_31, 6, x_28);
x_32 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_27, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___lambda__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
return x_18;
}
}
static lean_object* _init_l_MyNat_rfl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rfl", 3);
return x_1;
}
}
static lean_object* _init_l_MyNat_rfl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_MyNat_rewriteSeq___closed__1;
x_2 = l_MyNat_rfl___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_MyNat_rfl___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_MyNat_rfl___closed__1;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_MyNat_rfl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_MyNat_rfl___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_MyNat_rfl___closed__3;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_MyNat_rfl() {
_start:
{
lean_object* x_1; 
x_1 = l_MyNat_rfl___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_MyNat_evalRfl___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 5);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = 2;
lean_ctor_set_uint8(x_11, 5, x_20);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_15);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set(x_21, 4, x_17);
lean_ctor_set(x_21, 5, x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_MVarId_refl(x_12, x_21, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Tactic_replaceMainGoal(x_24, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_40 = lean_ctor_get_uint8(x_11, 0);
x_41 = lean_ctor_get_uint8(x_11, 1);
x_42 = lean_ctor_get_uint8(x_11, 2);
x_43 = lean_ctor_get_uint8(x_11, 3);
x_44 = lean_ctor_get_uint8(x_11, 4);
x_45 = lean_ctor_get_uint8(x_11, 6);
x_46 = lean_ctor_get_uint8(x_11, 7);
x_47 = lean_ctor_get_uint8(x_11, 8);
x_48 = lean_ctor_get_uint8(x_11, 9);
x_49 = lean_ctor_get_uint8(x_11, 10);
x_50 = lean_ctor_get_uint8(x_11, 11);
x_51 = lean_ctor_get_uint8(x_11, 12);
lean_dec(x_11);
x_52 = 2;
x_53 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_53, 0, x_40);
lean_ctor_set_uint8(x_53, 1, x_41);
lean_ctor_set_uint8(x_53, 2, x_42);
lean_ctor_set_uint8(x_53, 3, x_43);
lean_ctor_set_uint8(x_53, 4, x_44);
lean_ctor_set_uint8(x_53, 5, x_52);
lean_ctor_set_uint8(x_53, 6, x_45);
lean_ctor_set_uint8(x_53, 7, x_46);
lean_ctor_set_uint8(x_53, 8, x_47);
lean_ctor_set_uint8(x_53, 9, x_48);
lean_ctor_set_uint8(x_53, 10, x_49);
lean_ctor_set_uint8(x_53, 11, x_50);
lean_ctor_set_uint8(x_53, 12, x_51);
x_54 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_14);
lean_ctor_set(x_54, 2, x_15);
lean_ctor_set(x_54, 3, x_16);
lean_ctor_set(x_54, 4, x_17);
lean_ctor_set(x_54, 5, x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_55 = l_Lean_MVarId_refl(x_12, x_54, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = l_Lean_Elab_Tactic_replaceMainGoal(x_57, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_ctor_get(x_55, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_55, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_69 = x_55;
} else {
 lean_dec_ref(x_55);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_10);
if (x_71 == 0)
{
return x_10;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_10, 0);
x_73 = lean_ctor_get(x_10, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_10);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
static lean_object* _init_l_MyNat_evalRfl___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_MyNat_evalRfl___rarg___lambda__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MyNat_evalRfl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_MyNat_evalRfl___rarg___closed__1;
x_11 = l_Lean_Elab_Tactic_withMainContext___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_MyNat_evalRfl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_MyNat_evalRfl___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MyNat_evalRfl___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MyNat_evalRfl(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Lean_Expr_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_MyNat_Addition(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NNG_Modifications_Tactics(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Lean_Expr_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_MyNat_Addition(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_MyNat_rewriteSeq___closed__1 = _init_l_MyNat_rewriteSeq___closed__1();
lean_mark_persistent(l_MyNat_rewriteSeq___closed__1);
l_MyNat_rewriteSeq___closed__2 = _init_l_MyNat_rewriteSeq___closed__2();
lean_mark_persistent(l_MyNat_rewriteSeq___closed__2);
l_MyNat_rewriteSeq___closed__3 = _init_l_MyNat_rewriteSeq___closed__3();
lean_mark_persistent(l_MyNat_rewriteSeq___closed__3);
l_MyNat_rewriteSeq___closed__4 = _init_l_MyNat_rewriteSeq___closed__4();
lean_mark_persistent(l_MyNat_rewriteSeq___closed__4);
l_MyNat_rewriteSeq___closed__5 = _init_l_MyNat_rewriteSeq___closed__5();
lean_mark_persistent(l_MyNat_rewriteSeq___closed__5);
l_MyNat_rewriteSeq___closed__6 = _init_l_MyNat_rewriteSeq___closed__6();
lean_mark_persistent(l_MyNat_rewriteSeq___closed__6);
l_MyNat_rewriteSeq___closed__7 = _init_l_MyNat_rewriteSeq___closed__7();
lean_mark_persistent(l_MyNat_rewriteSeq___closed__7);
l_MyNat_rewriteSeq___closed__8 = _init_l_MyNat_rewriteSeq___closed__8();
lean_mark_persistent(l_MyNat_rewriteSeq___closed__8);
l_MyNat_rewriteSeq___closed__9 = _init_l_MyNat_rewriteSeq___closed__9();
lean_mark_persistent(l_MyNat_rewriteSeq___closed__9);
l_MyNat_rewriteSeq___closed__10 = _init_l_MyNat_rewriteSeq___closed__10();
lean_mark_persistent(l_MyNat_rewriteSeq___closed__10);
l_MyNat_rewriteSeq___closed__11 = _init_l_MyNat_rewriteSeq___closed__11();
lean_mark_persistent(l_MyNat_rewriteSeq___closed__11);
l_MyNat_rewriteSeq___closed__12 = _init_l_MyNat_rewriteSeq___closed__12();
lean_mark_persistent(l_MyNat_rewriteSeq___closed__12);
l_MyNat_rewriteSeq___closed__13 = _init_l_MyNat_rewriteSeq___closed__13();
lean_mark_persistent(l_MyNat_rewriteSeq___closed__13);
l_MyNat_rewriteSeq___closed__14 = _init_l_MyNat_rewriteSeq___closed__14();
lean_mark_persistent(l_MyNat_rewriteSeq___closed__14);
l_MyNat_rewriteSeq___closed__15 = _init_l_MyNat_rewriteSeq___closed__15();
lean_mark_persistent(l_MyNat_rewriteSeq___closed__15);
l_MyNat_rewriteSeq = _init_l_MyNat_rewriteSeq();
lean_mark_persistent(l_MyNat_rewriteSeq);
l_MyNat_evalRewriteSeq___lambda__2___closed__1 = _init_l_MyNat_evalRewriteSeq___lambda__2___closed__1();
lean_mark_persistent(l_MyNat_evalRewriteSeq___lambda__2___closed__1);
l_MyNat_evalRewriteSeq___lambda__2___closed__2 = _init_l_MyNat_evalRewriteSeq___lambda__2___closed__2();
lean_mark_persistent(l_MyNat_evalRewriteSeq___lambda__2___closed__2);
l_MyNat_evalRewriteSeq___lambda__2___closed__3 = _init_l_MyNat_evalRewriteSeq___lambda__2___closed__3();
lean_mark_persistent(l_MyNat_evalRewriteSeq___lambda__2___closed__3);
l_MyNat_evalRewriteSeq___lambda__2___closed__4 = _init_l_MyNat_evalRewriteSeq___lambda__2___closed__4();
lean_mark_persistent(l_MyNat_evalRewriteSeq___lambda__2___closed__4);
l_MyNat_evalRewriteSeq___lambda__2___closed__5 = _init_l_MyNat_evalRewriteSeq___lambda__2___closed__5();
lean_mark_persistent(l_MyNat_evalRewriteSeq___lambda__2___closed__5);
l_MyNat_evalRewriteSeq___lambda__3___closed__1 = _init_l_MyNat_evalRewriteSeq___lambda__3___closed__1();
lean_mark_persistent(l_MyNat_evalRewriteSeq___lambda__3___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Parser_Tactic_ElimApp_evalNames___spec__4___closed__9);
l_Lean_Parser_Tactic_ElimApp_evalNames___closed__1 = _init_l_Lean_Parser_Tactic_ElimApp_evalNames___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_ElimApp_evalNames___closed__1);
l_MyNat_induction___closed__1 = _init_l_MyNat_induction___closed__1();
lean_mark_persistent(l_MyNat_induction___closed__1);
l_MyNat_induction___closed__2 = _init_l_MyNat_induction___closed__2();
lean_mark_persistent(l_MyNat_induction___closed__2);
l_MyNat_induction___closed__3 = _init_l_MyNat_induction___closed__3();
lean_mark_persistent(l_MyNat_induction___closed__3);
l_MyNat_induction___closed__4 = _init_l_MyNat_induction___closed__4();
lean_mark_persistent(l_MyNat_induction___closed__4);
l_MyNat_induction___closed__5 = _init_l_MyNat_induction___closed__5();
lean_mark_persistent(l_MyNat_induction___closed__5);
l_MyNat_induction___closed__6 = _init_l_MyNat_induction___closed__6();
lean_mark_persistent(l_MyNat_induction___closed__6);
l_MyNat_induction___closed__7 = _init_l_MyNat_induction___closed__7();
lean_mark_persistent(l_MyNat_induction___closed__7);
l_MyNat_induction___closed__8 = _init_l_MyNat_induction___closed__8();
lean_mark_persistent(l_MyNat_induction___closed__8);
l_MyNat_induction___closed__9 = _init_l_MyNat_induction___closed__9();
lean_mark_persistent(l_MyNat_induction___closed__9);
l_MyNat_induction___closed__10 = _init_l_MyNat_induction___closed__10();
lean_mark_persistent(l_MyNat_induction___closed__10);
l_MyNat_induction___closed__11 = _init_l_MyNat_induction___closed__11();
lean_mark_persistent(l_MyNat_induction___closed__11);
l_MyNat_induction___closed__12 = _init_l_MyNat_induction___closed__12();
lean_mark_persistent(l_MyNat_induction___closed__12);
l_MyNat_induction___closed__13 = _init_l_MyNat_induction___closed__13();
lean_mark_persistent(l_MyNat_induction___closed__13);
l_MyNat_induction___closed__14 = _init_l_MyNat_induction___closed__14();
lean_mark_persistent(l_MyNat_induction___closed__14);
l_MyNat_induction___closed__15 = _init_l_MyNat_induction___closed__15();
lean_mark_persistent(l_MyNat_induction___closed__15);
l_MyNat_induction___closed__16 = _init_l_MyNat_induction___closed__16();
lean_mark_persistent(l_MyNat_induction___closed__16);
l_MyNat_induction___closed__17 = _init_l_MyNat_induction___closed__17();
lean_mark_persistent(l_MyNat_induction___closed__17);
l_MyNat_induction___closed__18 = _init_l_MyNat_induction___closed__18();
lean_mark_persistent(l_MyNat_induction___closed__18);
l_MyNat_induction___closed__19 = _init_l_MyNat_induction___closed__19();
lean_mark_persistent(l_MyNat_induction___closed__19);
l_MyNat_induction___closed__20 = _init_l_MyNat_induction___closed__20();
lean_mark_persistent(l_MyNat_induction___closed__20);
l_MyNat_induction___closed__21 = _init_l_MyNat_induction___closed__21();
lean_mark_persistent(l_MyNat_induction___closed__21);
l_MyNat_induction___closed__22 = _init_l_MyNat_induction___closed__22();
lean_mark_persistent(l_MyNat_induction___closed__22);
l_MyNat_induction___closed__23 = _init_l_MyNat_induction___closed__23();
lean_mark_persistent(l_MyNat_induction___closed__23);
l_MyNat_induction___closed__24 = _init_l_MyNat_induction___closed__24();
lean_mark_persistent(l_MyNat_induction___closed__24);
l_MyNat_induction = _init_l_MyNat_induction();
lean_mark_persistent(l_MyNat_induction);
l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___lambda__1___closed__1 = _init_l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___lambda__1___closed__1);
l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___closed__1 = _init_l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___closed__1);
l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___closed__2 = _init_l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic___aux__NNG__Modifications__Tactics______elabRules__Lean__Parser__Tactic____root____MyNat__induction__1___closed__2);
l_MyNat_rfl___closed__1 = _init_l_MyNat_rfl___closed__1();
lean_mark_persistent(l_MyNat_rfl___closed__1);
l_MyNat_rfl___closed__2 = _init_l_MyNat_rfl___closed__2();
lean_mark_persistent(l_MyNat_rfl___closed__2);
l_MyNat_rfl___closed__3 = _init_l_MyNat_rfl___closed__3();
lean_mark_persistent(l_MyNat_rfl___closed__3);
l_MyNat_rfl___closed__4 = _init_l_MyNat_rfl___closed__4();
lean_mark_persistent(l_MyNat_rfl___closed__4);
l_MyNat_rfl = _init_l_MyNat_rfl();
lean_mark_persistent(l_MyNat_rfl);
l_MyNat_evalRfl___rarg___closed__1 = _init_l_MyNat_evalRfl___rarg___closed__1();
lean_mark_persistent(l_MyNat_evalRfl___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
