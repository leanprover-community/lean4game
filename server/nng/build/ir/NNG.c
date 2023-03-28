// Lean compiler output
// Module: NNG
// Imports: Init GameServer.Commands NNG.Levels.Tutorial NNG.Levels.Addition NNG.Levels.Multiplication NNG.Levels.Power NNG.Levels.Function NNG.Levels.Proposition NNG.Levels.AdvProposition NNG.Levels.AdvAddition NNG.Levels.AdvMultiplication NNG.Levels.Inequality
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_GameServer_Commands(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Tutorial(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Addition(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Multiplication(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Power(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Function(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Proposition(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_AdvProposition(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_AdvAddition(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_AdvMultiplication(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NNG(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GameServer_Commands(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Tutorial(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Addition(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Multiplication(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Power(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Function(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Proposition(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_AdvProposition(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_AdvAddition(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_AdvMultiplication(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
