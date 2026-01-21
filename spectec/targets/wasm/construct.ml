open Wasm_interpreter.Types
open Wasm_interpreter.Value
open Wasm_interpreter.Ast
open Wasm_interpreter.Source
open Wasm_interpreter
open Lang.Il.Utils

module Il = Lang.Il
module Value = Il.Value
module Make = Value.Make

(* il_of_* 함수는 il.value를 반환해야 한다. *)

let default_table_max = 4294967295L
let default_memory_max = 65536L

let listV l = Il.ListV (l)

let optV opt = Il.OptV (opt)

let il_of_list s f l = List.map f l |> Make.list (iter_t List (var_t s))
let il_of_seq s f seq = List.of_seq seq |> il_of_list s f
let il_of_opt s f opt = Option.map f opt |> Make.opt (iter_t Opt (var_t s))

let il_of_final = function
  | NoFinal ->
      [ Term "NoFinal" ] #@ "final"
  | Final ->
      [ Term "Final" ] #@ "final"

let bigint_of_z_nat z =
  assert (z >= Z.zero);
  Bigint.of_zarith_bigint z

let bigint_of_nat32 i32 =
  Z.of_int32_unsigned i32 |> bigint_of_z_nat

let bigint_of_nat64 i64 =
  Z.of_int64_unsigned i64 |> bigint_of_z_nat

let bigint_of_nat i = Z.of_int i |> bigint_of_z_nat

(*
let bigint_of_byte byte = Char.code byte |> bigint_of_nat

let il_of_bytes bytes_ = String.to_seq bytes_ |> Seq.map bigint_of_byte |> il_of_seq Value.nat (Seq.map bigint_of_byte)
*)
let il_of_idx s idx =
  bigint_of_nat32 idx.it |> Make.nat (var_t s)

let il_of_name name = Value.text (Utf8.encode name)

let string_of_abs_heap_type = function
  | AnyHT -> "AnyHT"
  | NoneHT -> "NoneHT"
  | EqHT -> "EqHT"
  | I31HT -> "I31HT"
  | StructHT -> "StructHT"
  | ArrayHT -> "ArrayHT"
  | FuncHT -> "FuncHT"
  | NoFuncHT -> "NoFuncHT"
  | ExnHT -> "ExnHT"
  | NoExnHT -> "NoExnHT"
  | ExternHT -> "ExternHT"
  | NoExternHT -> "NoExternHT"
  | BotHT -> "BotHT"
  | _ -> failwith "Not an abstract heap type"

let string_of_int_binop = function
  | IntOp.Add -> "IAdd"
  | IntOp.Sub -> "ISub"
  | IntOp.Mul -> "IMul"
  | IntOp.DivS -> "IDivS"
  | IntOp.DivU -> "IDivU"
  | IntOp.RemS -> "IRemS"
| IntOp.RemU -> "IRemU"
  | IntOp.And -> "IAnd"
  | IntOp.Or -> "IOr"
  | IntOp.Xor -> "IXor"
  | IntOp.Shl -> "IShl"
  | IntOp.ShrS -> "IShrS"
  | IntOp.ShrU -> "IShrU"
  | IntOp.Rotl -> "IRotl"
  | IntOp.Rotr -> "IRotr"

let string_of_float_binop = function
  | FloatOp.Add -> "FAdd"
  | FloatOp.Sub -> "FSub"
  | FloatOp.Mul -> "FMul"
  | FloatOp.Div -> "FDiv"
  | FloatOp.Min -> "FMin"
  | FloatOp.Max -> "FMax"
| FloatOp.CopySign -> "FCopysign"

(* better name for this function? *)
let rec il_of_typeuse = function
  | StatX i ->
    let symbols = [ Term "StatX"; NT (bigint_of_nat32 i |> Make.nat (var_t "typeidx")) ] in
    symbols #@ "typevar"
  | RecX i ->
    let symbols = [ Term "RecX"; NT (bigint_of_nat32 i |> Make.nat (var_t "typeidx")) ] in
    symbols #@ "typevar"

and il_of_def_type = function
  | DefT (rt, i) ->
    let symbols = [ Term "DefT"; NT (il_of_rec_type rt); NT (Value.nat (bigint_of_nat32 i)) ] in
    symbols #@ "deftype"

and il_of_heap_type = function
  | VarHT var ->
    let symbols = [ Term "VarHT"; NT (il_of_typeuse var) ] in
    symbols #@ "heaptype"
  | DefHT dt ->
    let symbols = [ Term "DefHT"; NT (il_of_def_type dt) ] in
    symbols #@ "heaptype"
  | ht ->
    [ Term (string_of_abs_heap_type ht) ] #@ "heaptype"

and il_of_mut = function
  | Cons ->
    [ Term "Cons" ] #@ "mut"
  | Var ->
[ Term "Var" ] #@ "mut"

and il_of_num_type = function
  | I32T ->
    [ Term "I32T" ] #@ "numtype"
  | I64T ->
    [ Term "I64T" ] #@ "numtype"
  | F32T ->
    [ Term "F32T" ] #@ "numtype"
  | F64T ->
    [ Term "F64T" ] #@ "numtype"

and il_of_null = function
  | NoNull ->
    [ Term "NoNull" ] #@ "null"
  | Null ->
    [ Term "Null" ] #@ "null"

and il_of_ref_type (null, ht) =
  let symbols =
    [ NT (il_of_null null); NT (il_of_heap_type ht) ] in
  symbols #@ "reftype"

and il_of_vec_type = function
  | V128T ->
    [ Term "V128T" ] #@ "vectype"

and il_of_val_type = function
  | NumT nt ->
    let symbols = [ Term "NumT"; NT (il_of_num_type nt) ] in
    symbols #@ "valtype"
  | RefT rt ->
    let symbols = [ Term "RefT"; NT (il_of_ref_type rt) ] in
    symbols #@ "valtype"
  | VecT vt ->
    let symbols = [ Term "VecT"; NT (il_of_vec_type vt) ] in
    symbols #@ "valtype"
  | BotT ->
    [ Term "BotT" ] #@ "valtype"

and il_of_pack_type = function
  | Pack.Pack8 ->
    [ Term "I8" ] #@ "packtype"
  | Pack.Pack16 ->
    [ Term "I16" ] #@ "packtype"
  | _ -> failwith "invalid pack type"

and il_of_storage_type = function
  | ValStorageT vt ->
    let symbols = [ Term "ValStorageT"; NT (il_of_val_type vt) ] in
    symbols #@ "storagetype"
  | PackStorageT pt ->
    let symbols = [ Term "PackStorageT"; NT (il_of_pack_type pt) ] in
    symbols #@ "storagetype"

and il_of_field_type = function
  | FieldT (mut, st) ->
    let symbols = [ Term "FieldT"; NT (il_of_mut mut); NT (il_of_storage_type st) ] in
    symbols #@ "fieldtype"

and il_of_struct_type = function
  | StructT ftl ->
      let symbols = [ Term "StructT"; NT (il_of_list "fieldtype" il_of_field_type ftl) ] in
      symbols #@ "structtype"

and il_of_array_type = function
  | ArrayT ft ->
      let symbols = [ Term "ArrayT"; NT (il_of_field_type ft) ] in
      symbols #@ "arraytype"

and il_of_result_type rt =
  il_of_list "valtype" il_of_val_type rt

and il_of_func_type = function
  | FuncT (rt1, rt2) ->
      let symbols = [ Term "FuncT"; NT (il_of_result_type rt1); NT (il_of_result_type rt2) ] in
      symbols #@ "functype"

and il_of_str_type = function
  | DefStructT st ->
    let symbols = [ Term "DefStructT"; NT (il_of_struct_type st) ] in
    symbols #@ "strtype"
  | DefArrayT arrt ->
    let symbols = [ Term "DefArrayT"; NT (il_of_array_type arrt) ] in
    symbols #@ "strtype"
  | DefFuncT ft ->
    let symbols = [ Term "DefFuncT"; NT (il_of_func_type ft) ] in
    symbols #@ "strtype"

and il_of_sub_type = function
  | SubT (fin, htl, strt) ->
    let symbols = [ Term "SubT"; NT (il_of_final fin); NT (il_of_list "heaptype" il_of_heap_type htl); NT (il_of_str_type strt) ] in
      symbols #@ "subtype"

and il_of_rec_type = function
  | RecT stl ->
    let symbols = [ Term "RecT"; NT (il_of_list "subtype" il_of_sub_type stl) ] in
      symbols #@ "rectype"

and il_of_global_type = function
  | GlobalT (mut, vt) ->
    let symbols = [ Term "GlobalT"; NT (il_of_mut mut); NT (il_of_val_type vt) ] in
    symbols #@ "globaltype"

and il_of_addr_type = function
  | I32AT ->
    [ Term "I32AT" ] #@ "addrtype"
  | I64AT ->
    [ Term "I64AT" ] #@ "addrtype"

and il_of_limits default limits =
  let max =
    match limits.max with
    | Some v -> Value.nat (bigint_of_nat64 v)
    | None -> Value.nat (bigint_of_nat64 default) in
  Make.record (var_t "limits") [
    (wrap_atom "MIN", Value.nat (bigint_of_nat64 limits.min));
    (wrap_atom "MAX", max) ]

and il_of_table_type = function
  | TableT (at, limits, rt) ->
    let symbols = [ Term "TableT"; NT (il_of_addr_type at); NT (il_of_limits default_table_max limits); NT (il_of_ref_type rt) ] in
    symbols #@ "tabletype"

and il_of_memory_type = function
  | MemoryT (at, limits) ->
    let symbols = [ Term "MemoryT"; NT (il_of_addr_type at); NT (il_of_limits default_memory_max limits) ] in
    symbols #@ "memtype"

let il_of_op f1 f2 = function
  | I32 op ->
    let v = f1 op in
    let (id, _, _) = flatten_case_v v in
    let symbols = [ Term "I32"; NT v ] in
    symbols #@ id
  | I64 op ->
    let v = f1 op in
    let (id, _, _) = flatten_case_v v in
    let symbols = [ Term "I64"; NT v ] in
    symbols #@ id
  | F32 op ->
    let v = f2 op in
    let (id, _, _) = flatten_case_v v in
    let symbols = [ Term "F32"; NT v ] in
    symbols #@ id
  | F64 op ->
    let v = f2 op in
    let (id, _, _) = flatten_case_v v in
    let symbols = [ Term "F64"; NT v ] in
    symbols #@ id

let il_of_int_binop ibinop =
  [ Term (string_of_int_binop ibinop) ] #@ "ibinop"

let il_of_float_binop fbinop =
  [ Term (string_of_float_binop fbinop) ] #@ "fbinop"

let il_of_binop = il_of_op il_of_int_binop il_of_float_binop

let il_of_instr instr =
  match instr.it with
  | Binary op ->
    let symbols = [ Term "BINOP"; NT (il_of_binop op) ] in
    symbols #@ "instr"
  | LocalGet idx ->
    let symbols = [ Term "LOCAL.GET"; NT (il_of_idx "localidx" idx) ] in
    symbols #@ "instr"
  | _ -> failwith "il_of_instr: not implemented yet"

let il_of_const const =
    il_of_list "instr" il_of_instr const.it
(* Construct module *)

let il_of_type type_ =
  il_of_rec_type type_.it

let il_of_global global =
  Make.record (var_t "global") [
    (wrap_atom "GTYPE", il_of_global_type global.it.gtype);
    (wrap_atom "GINIT", il_of_const global.it.ginit); ]

let il_of_table table =
  Make.record (var_t "table") [
    (wrap_atom "TTYPE", il_of_table_type table.it.ttype);
    (wrap_atom "TINIT", il_of_const table.it.tinit); ]

let il_of_memory memory =
  Make.record (var_t "memory") [
    (wrap_atom "MTYPE", il_of_memory_type memory.it.mtype) ]

let il_of_tag tag =
  Make.record (var_t "tag") [
    (wrap_atom "TGTYPE", il_of_idx "typeidx" tag.it.tgtype) ]

let il_of_local local =
  Make.record (var_t "local") [
    (wrap_atom "LTYPE", il_of_val_type local.it.ltype) ]

let il_of_func func =
  Make.record (var_t "func") [
    (wrap_atom "FTYPE", il_of_idx "typeidx" func.it.ftype);
    (wrap_atom "LOCALS", il_of_list "local" il_of_local func.it.locals);
    (wrap_atom "BODY", il_of_list "instr" il_of_instr func.it.body); ]

let il_of_start start =
  Make.record (var_t "start") [
    (wrap_atom "SFUNC", il_of_idx "funcidx" start.it.sfunc) ]

let il_of_segment segment =
  match segment.it with
  | Passive ->
    [ Term "Passive" ] #@ "segmentmode"
  | Active { index; offset } ->
    let symbols =
      [ Term "Active"; NT (Make.record (var_t "active") [(wrap_atom "INDEX", Value.nat (bigint_of_nat32 index.it)); (wrap_atom "OFFSET", il_of_const offset)]) ] in
    symbols #@ "segmentmode"
  | Declarative ->
    [ Term "Declarative" ] #@ "segmentmode"

let il_of_elem elem =
  Make.record (var_t "elem") [
    (wrap_atom "ETYPE", il_of_ref_type elem.it.etype);
    (wrap_atom "EINIT", il_of_list "const" il_of_const elem.it.einit);
    (wrap_atom "EMODE", il_of_segment elem.it.emode); ]

let il_of_data data =
  Make.record (var_t "data") [
    (wrap_atom "DINIT", Value.text data.it.dinit);
    (wrap_atom "DMODE", il_of_segment data.it.dmode); ]

let il_of_import_desc module_ idesc =
  match idesc.it with
  | FuncImport x ->
    let dts = def_types_of module_ in
    let dt = x.it |> Int32.to_int |> List.nth dts |> il_of_def_type in
    let symbols = [ Term "FuncImport"; NT dt ] in
    symbols #@ "importdesc"
  | TableImport tt ->
    let symbols = [ Term "TableImport"; NT (il_of_table_type tt) ] in
    symbols #@ "importdesc"
  | MemoryImport mt ->
    let symbols = [ Term "MemoryImport"; NT (il_of_memory_type mt) ] in
    symbols #@ "importdesc"
  | GlobalImport gt ->
    let symbols = [ Term "GlobalImport"; NT (il_of_global_type gt) ] in
    symbols #@ "importdesc"
  | TagImport x ->
    let dts = def_types_of module_ in
    let dt = x.it |> Int32.to_int |> List.nth dts |> il_of_def_type in
    let symbols = [ Term "TagImport"; NT dt ] in
    symbols #@ "importdesc"

let il_of_import module_ import =
  Make.record (var_t "import") [
    (wrap_atom "MODULENAME", il_of_name import.it.module_name);
    (wrap_atom "ITEMNAME", il_of_name import.it.item_name);
    (wrap_atom "IDESC", il_of_import_desc module_ import.it.idesc); ]

let il_of_export_desc export_desc =
  match export_desc.it with
  | FuncExport idx ->
    let symbols = [ Term "FuncExport"; NT (il_of_idx "funcidx" idx) ] in
    symbols #@ "exportdesc"
  | TableExport idx ->
    let symbols = [ Term "TableExport"; NT (il_of_idx "tableidx" idx) ] in
    symbols #@ "exportdesc"
  | MemoryExport idx ->
    let symbols = [ Term "MemExport"; NT (il_of_idx "memidx" idx) ] in
    symbols #@ "exportdesc"
  | GlobalExport idx ->
    let symbols = [ Term "GlobalExport"; NT (il_of_idx "globalidx" idx) ] in
    symbols #@ "exportdesc"
  | TagExport idx ->
    let symbols = [ Term "TagExport"; NT (il_of_idx "tagidx" idx) ] in
    symbols #@ "exportdesc"

let il_of_export export =
  Make.record (var_t "export") [
    (wrap_atom "NAME", il_of_name export.it.name);
    (wrap_atom "EDESC", il_of_export_desc export.it.edesc); ]

let il_of_module module_ : Lang__Il__.Types.value =
  Make.record (var_t "module") [
    (wrap_atom "TYPES", il_of_list "type" il_of_type module_.it.types);
    (wrap_atom "GLOBALS", il_of_list "global" il_of_global module_.it.globals);
    (wrap_atom "TABLES", il_of_list "table" il_of_table module_.it.tables);
    (wrap_atom "MEMS", il_of_list "memory" il_of_memory module_.it.memories);
    (wrap_atom "TAGS", il_of_list "tag" il_of_tag module_.it.tags);
    (wrap_atom "FUNCS", il_of_list "func" il_of_func module_.it.funcs);
    (wrap_atom "START", il_of_opt "start" il_of_start module_.it.start);
    (wrap_atom "ELEMS", il_of_list "elem" il_of_elem module_.it.elems);
    (wrap_atom "DATAS", il_of_list "data" il_of_data module_.it.datas);
    (wrap_atom "IMPORTS", il_of_list "import" (il_of_import module_) module_.it.imports);
    (wrap_atom "EXPORTS", il_of_list "export" il_of_export module_.it.exports);
  ]
