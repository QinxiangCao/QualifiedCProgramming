#include <windows.h>

#include <stdio.h>
#include <string.h>

static char stdlib_path[MAX_PATH];

static void init_stdlib_path(void) {
  char exe_path[MAX_PATH];
  char *last_slash;

  DWORD len = GetModuleFileNameA(NULL, exe_path, sizeof(exe_path));
  if (len == 0 || len >= sizeof(exe_path)) {
    strcpy(stdlib_path, ".");
    return;
  }

  last_slash = strrchr(exe_path, '\\');
  if (last_slash == NULL) {
    strcpy(stdlib_path, ".");
    return;
  }

  *last_slash = '\0';
  last_slash = strrchr(exe_path, '\\');
  if (last_slash == NULL) {
    strcpy(stdlib_path, ".");
    return;
  }

  *last_slash = '\0';
  snprintf(stdlib_path, sizeof(stdlib_path), "%s\\lib\\ocaml", exe_path);
}

static const char *config_var(const char *name) {
  if (strcmp(name, "version") == 0)
    return "4.14.1";
  if (strcmp(name, "standard_library") == 0)
    return stdlib_path;
  if (strcmp(name, "standard_library_default") == 0)
    return stdlib_path;
  if (strcmp(name, "ccomp_type") == 0)
    return "msvc";
  if (strcmp(name, "c_compiler") == 0)
    return "cl";
  if (strcmp(name, "architecture") == 0)
    return "amd64";
  if (strcmp(name, "model") == 0)
    return "default";
  if (strcmp(name, "int_size") == 0)
    return "63";
  if (strcmp(name, "word_size") == 0)
    return "64";
  if (strcmp(name, "system") == 0)
    return "win32";
  if (strcmp(name, "os_type") == 0)
    return "Win32";
  if (strcmp(name, "ext_exe") == 0)
    return ".exe";
  if (strcmp(name, "ext_obj") == 0)
    return ".obj";
  if (strcmp(name, "ext_asm") == 0)
    return ".asm";
  if (strcmp(name, "ext_lib") == 0)
    return ".lib";
  if (strcmp(name, "ext_dll") == 0)
    return ".dll";
  if (strcmp(name, "native_compiler") == 0)
    return "false";
  if (strcmp(name, "supports_shared_libraries") == 0)
    return "false";
  if (strcmp(name, "systhread_supported") == 0)
    return "false";
  if (strcmp(name, "exec_magic_number") == 0)
    return "Caml1999X031";
  if (strcmp(name, "cmi_magic_number") == 0)
    return "Caml1999I031";
  if (strcmp(name, "cmo_magic_number") == 0)
    return "Caml1999O031";
  if (strcmp(name, "cma_magic_number") == 0)
    return "Caml1999A031";
  if (strcmp(name, "cmx_magic_number") == 0)
    return "Caml1999Y031";
  if (strcmp(name, "cmxa_magic_number") == 0)
    return "Caml1999Z031";
  if (strcmp(name, "ast_impl_magic_number") == 0)
    return "Caml1999M031";
  if (strcmp(name, "ast_intf_magic_number") == 0)
    return "Caml1999N031";
  if (strcmp(name, "cmxs_magic_number") == 0)
    return "Caml2007D003";
  if (strcmp(name, "cmt_magic_number") == 0)
    return "Caml1999T031";
  return "";
}

static void print_config(void) {
  printf("version: 4.14.1\n");
  printf("standard_library: %s\n", stdlib_path);
  printf("standard_library_default: %s\n", stdlib_path);
  printf("ccomp_type: msvc\n");
  printf("c_compiler: cl\n");
  printf("ocamlc_cflags:\n");
  printf("ocamlc_cppflags:\n");
  printf("ocamlopt_cflags:\n");
  printf("ocamlopt_cppflags:\n");
  printf("bytecomp_c_compiler: cl\n");
  printf("native_c_compiler: cl\n");
  printf("bytecomp_c_libraries:\n");
  printf("native_c_libraries:\n");
  printf("native_pack_linker: link\n");
  printf("architecture: amd64\n");
  printf("model: default\n");
  printf("int_size: 63\n");
  printf("word_size: 64\n");
  printf("system: win32\n");
  printf("asm:\n");
  printf("asm_cfi_supported: false\n");
  printf("with_frame_pointers: false\n");
  printf("ext_exe: .exe\n");
  printf("ext_obj: .obj\n");
  printf("ext_asm: .asm\n");
  printf("ext_lib: .lib\n");
  printf("ext_dll: .dll\n");
  printf("os_type: Win32\n");
  printf("default_executable_name: a.exe\n");
  printf("systhread_supported: false\n");
  printf("host: x86_64-pc-windows\n");
  printf("target: x86_64-pc-windows\n");
  printf("flambda: false\n");
  printf("profiling: false\n");
  printf("spacetime: false\n");
  printf("safe_string: true\n");
  printf("default_safe_string: true\n");
  printf("flat_float_array: true\n");
  printf("function_sections: false\n");
  printf("afl_instrument: false\n");
  printf("windows_unicode: true\n");
  printf("supports_shared_libraries: false\n");
  printf("naked_pointers: false\n");
  printf("native_compiler: false\n");
  printf("parameterised_modules: false\n");
  printf("exec_magic_number: Caml1999X031\n");
  printf("cmi_magic_number: Caml1999I031\n");
  printf("cmo_magic_number: Caml1999O031\n");
  printf("cma_magic_number: Caml1999A031\n");
  printf("cmx_magic_number: Caml1999Y031\n");
  printf("cmxa_magic_number: Caml1999Z031\n");
  printf("ast_impl_magic_number: Caml1999M031\n");
  printf("ast_intf_magic_number: Caml1999N031\n");
  printf("cmxs_magic_number: Caml2007D003\n");
  printf("cmt_magic_number: Caml1999T031\n");
}

int main(int argc, char **argv) {
  init_stdlib_path();

  if (argc == 2 && strcmp(argv[1], "-version") == 0) {
    printf("4.14.1\n");
    return 0;
  }

  if (argc == 2 && strcmp(argv[1], "-vnum") == 0) {
    printf("4.14.1\n");
    return 0;
  }

  if (argc == 2 && strcmp(argv[1], "-where") == 0) {
    printf("%s\n", stdlib_path);
    return 0;
  }

  if (argc == 3 && strcmp(argv[1], "-config-var") == 0) {
    printf("%s\n", config_var(argv[2]));
    return 0;
  }

  if (argc == 2 && strcmp(argv[1], "-config") == 0) {
    print_config();
    return 0;
  }

  fprintf(stderr, "fake ocamlc: this shim only supports Dune probing, not "
                  "OCaml compilation.\n");
  return 2;
}
