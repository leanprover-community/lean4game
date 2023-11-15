#include <stdio.h>
#include <lean/lean.h>

extern lean_object* game_send_message(lean_object*, lean_object*);

// see https://leanprover.github.io/lean4/doc/dev/ffi.html#initialization
extern void lean_initialize_runtime_module();
extern void lean_initialize();
extern void lean_io_mark_end_initialization();
extern lean_object * initialize_GameServer_WasmServer(uint8_t builtin, lean_object *);

int main() {
  lean_initialize();
  lean_initialize_runtime_module();
  lean_object * res;
  // use same default as for Lean executables
  uint8_t builtin = 1;
  lean_object * io_world = lean_io_mk_world();
  res = initialize_GameServer_WasmServer(builtin, io_world);
  if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
  } else {
      lean_io_result_show_error(res);
      lean_dec(res);
      return 1;  // do not access Lean declarations if initialization failed
  }
  lean_io_mark_end_initialization();
}

void send_message(char* msg){
  lean_object * s = lean_mk_string(msg);
  game_send_message(s, lean_io_mk_world());
}
