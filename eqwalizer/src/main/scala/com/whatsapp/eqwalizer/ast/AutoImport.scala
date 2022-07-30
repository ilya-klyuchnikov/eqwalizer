/* Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
 *
 * This source code is licensed under the Apache 2.0 license found in
 * the LICENSE file in the root directory of this source tree.
 */

package com.whatsapp.eqwalizer.ast

object AutoImport {
  // see erl_internal:bif/2 (both OTP 23 and 24 - they are identical)
  // TODO -  see D27999555 and D28026682:
  // There is only ONE module in WASERVER - wa_fbpkg which uses no_auto_import.
  val funs: Set[Id] = Set(
    Id("abs", 1),
    Id("apply", 2),
    Id("apply", 3),
    Id("atom_to_binary", 1),
    Id("atom_to_binary", 2),
    Id("atom_to_list", 1),
    Id("binary_part", 2),
    Id("binary_part", 3),
    Id("binary_to_atom", 1),
    Id("binary_to_atom", 2),
    Id("binary_to_existing_atom", 1),
    Id("binary_to_existing_atom", 2),
    Id("binary_to_integer", 1),
    Id("binary_to_integer", 2),
    Id("binary_to_float", 1),
    Id("binary_to_list", 1),
    Id("binary_to_list", 3),
    Id("binary_to_term", 1),
    Id("binary_to_term", 2),
    Id("bitsize", 1),
    Id("bit_size", 1),
    Id("bitstring_to_list", 1),
    Id("byte_size", 1),
    Id("ceil", 1),
    Id("check_old_code", 1),
    Id("check_process_code", 2),
    Id("check_process_code", 3),
    Id("date", 0),
    Id("delete_module", 1),
    Id("demonitor", 1),
    Id("demonitor", 2),
    Id("disconnect_node", 1),
    Id("element", 2),
    Id("erase", 0),
    Id("erase", 1),
    Id("error", 1),
    Id("error", 2),
    Id("exit", 1),
    Id("exit", 2),
    Id("float", 1),
    Id("float_to_list", 1),
    Id("float_to_list", 2),
    Id("float_to_binary", 1),
    Id("float_to_binary", 2),
    Id("floor", 1),
    Id("garbage_collect", 0),
    Id("garbage_collect", 1),
    Id("garbage_collect", 2),
    Id("get", 0),
    Id("get", 1),
    Id("get_keys", 0),
    Id("get_keys", 1),
    Id("group_leader", 0),
    Id("group_leader", 2),
    Id("halt", 0),
    Id("halt", 1),
    Id("halt", 2),
    Id("hd", 1),
    Id("integer_to_binary", 1),
    Id("integer_to_binary", 2),
    Id("integer_to_list", 1),
    Id("integer_to_list", 2),
    Id("iolist_size", 1),
    Id("iolist_to_binary", 1),
    Id("is_alive", 0),
    Id("is_process_alive", 1),
    Id("is_atom", 1),
    Id("is_boolean", 1),
    Id("is_binary", 1),
    Id("is_bitstring", 1),
    Id("is_float", 1),
    Id("is_function", 1),
    Id("is_function", 2),
    Id("is_integer", 1),
    Id("is_list", 1),
    Id("is_map", 1),
    Id("is_map_key", 2),
    Id("is_number", 1),
    Id("is_pid", 1),
    Id("is_port", 1),
    Id("is_reference", 1),
    Id("is_tuple", 1),
    Id("is_record", 2),
    Id("is_record", 3),
    Id("length", 1),
    Id("link", 1),
    Id("list_to_atom", 1),
    Id("list_to_binary", 1),
    Id("list_to_bitstring", 1),
    Id("list_to_existing_atom", 1),
    Id("list_to_float", 1),
    Id("list_to_integer", 1),
    Id("list_to_integer", 2),
    Id("list_to_pid", 1),
    Id("list_to_port", 1),
    Id("list_to_ref", 1),
    Id("list_to_tuple", 1),
    Id("load_module", 2),
    Id("make_ref", 0),
    Id("map_size", 1),
    Id("map_get", 2),
    Id("max", 2),
    Id("min", 2),
    Id("module_loaded", 1),
    Id("monitor", 2),
    Id("monitor_node", 2),
    Id("node", 0),
    Id("node", 1),
    Id("nodes", 0),
    Id("nodes", 1),
    Id("now", 0),
    Id("open_port", 2),
    Id("pid_to_list", 1),
    Id("port_to_list", 1),
    Id("port_close", 1),
    Id("port_command", 2),
    Id("port_command", 3),
    Id("port_connect", 2),
    Id("port_control", 3),
    Id("pre_loaded", 0),
    Id("process_flag", 2),
    Id("process_flag", 3),
    Id("process_info", 1),
    Id("process_info", 2),
    Id("processes", 0),
    Id("purge_module", 1),
    Id("put", 2),
    Id("ref_to_list", 1),
    Id("register", 2),
    Id("registered", 0),
    Id("round", 1),
    Id("self", 0),
    Id("setelement", 3),
    Id("size", 1),
    Id("spawn", 1),
    Id("spawn", 2),
    Id("spawn", 3),
    Id("spawn", 4),
    Id("spawn_link", 1),
    Id("spawn_link", 2),
    Id("spawn_link", 3),
    Id("spawn_link", 4),
    Id("spawn_request", 1),
    Id("spawn_request", 2),
    Id("spawn_request", 3),
    Id("spawn_request", 4),
    Id("spawn_request", 5),
    Id("spawn_request_abandon", 1),
    Id("spawn_monitor", 1),
    Id("spawn_monitor", 2),
    Id("spawn_monitor", 3),
    Id("spawn_monitor", 4),
    Id("spawn_opt", 2),
    Id("spawn_opt", 3),
    Id("spawn_opt", 4),
    Id("spawn_opt", 5),
    Id("split_binary", 2),
    Id("statistics", 1),
    Id("term_to_binary", 1),
    Id("term_to_binary", 2),
    Id("term_to_iovec", 1),
    Id("term_to_iovec", 2),
    Id("throw", 1),
    Id("time", 0),
    Id("tl", 1),
    Id("trunc", 1),
    Id("tuple_size", 1),
    Id("tuple_to_list", 1),
    Id("unlink", 1),
    Id("unregister", 1),
    Id("whereis", 1),
  )
}
