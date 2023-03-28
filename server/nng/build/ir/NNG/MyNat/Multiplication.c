// Lean compiler output
// Module: NNG.MyNat.Multiplication
// Imports: Init NNG.MyNat.Addition
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
LEAN_EXPORT lean_object* l_MyNat_instMulMyNat;
static lean_object* l_MyNat_instMulMyNat___closed__1;
lean_object* l_MyNat_myNatFromNat(lean_object*);
LEAN_EXPORT lean_object* l_MyNat_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MyNat_mul(lean_object*, lean_object*);
lean_object* l_MyNat_add(lean_object*, lean_object*);
static lean_object* l_MyNat_mul___closed__1;
static lean_object* _init_l_MyNat_mul___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_MyNat_myNatFromNat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MyNat_mul(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_MyNat_mul___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_MyNat_mul(x_1, x_4);
x_6 = l_MyNat_add(x_1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_MyNat_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MyNat_mul(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_MyNat_instMulMyNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_MyNat_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_MyNat_instMulMyNat() {
_start:
{
lean_object* x_1; 
x_1 = l_MyNat_instMulMyNat___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_MyNat_Addition(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NNG_MyNat_Multiplication(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_MyNat_Addition(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_MyNat_mul___closed__1 = _init_l_MyNat_mul___closed__1();
lean_mark_persistent(l_MyNat_mul___closed__1);
l_MyNat_instMulMyNat___closed__1 = _init_l_MyNat_instMulMyNat___closed__1();
lean_mark_persistent(l_MyNat_instMulMyNat___closed__1);
l_MyNat_instMulMyNat = _init_l_MyNat_instMulMyNat();
lean_mark_persistent(l_MyNat_instMulMyNat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
