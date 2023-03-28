// Lean compiler output
// Module: NNG.Levels.Inequality
// Imports: Init NNG.Levels.Inequality.Level_1 NNG.Levels.Inequality.Level_2 NNG.Levels.Inequality.Level_3 NNG.Levels.Inequality.Level_4 NNG.Levels.Inequality.Level_5 NNG.Levels.Inequality.Level_6 NNG.Levels.Inequality.Level_7 NNG.Levels.Inequality.Level_8 NNG.Levels.Inequality.Level_9 NNG.Levels.Inequality.Level_10 NNG.Levels.Inequality.Level_11 NNG.Levels.Inequality.Level_12 NNG.Levels.Inequality.Level_13 NNG.Levels.Inequality.Level_14 NNG.Levels.Inequality.Level_15 NNG.Levels.Inequality.Level_16 NNG.Levels.Inequality.Level_17
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
lean_object* initialize_NNG_Levels_Inequality_Level__1(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality_Level__2(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality_Level__3(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality_Level__4(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality_Level__5(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality_Level__6(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality_Level__7(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality_Level__8(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality_Level__9(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality_Level__10(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality_Level__11(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality_Level__12(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality_Level__13(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality_Level__14(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality_Level__15(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality_Level__16(uint8_t builtin, lean_object*);
lean_object* initialize_NNG_Levels_Inequality_Level__17(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_NNG_Levels_Inequality(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__1(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__2(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__3(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__4(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__5(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__6(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__7(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__8(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__9(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__10(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__11(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__12(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__13(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__14(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__15(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__16(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_NNG_Levels_Inequality_Level__17(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
