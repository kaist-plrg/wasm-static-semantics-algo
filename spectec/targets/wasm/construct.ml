open Wasm_interpreter.Types
open Wasm_interpreter.Value
open Wasm_interpreter.Ast
open Wasm_interpreter.Source
open Wasm_interpreter
open Lang.Il.Utils

module Il = Lang.Il
module Value = Il.Value
module Make = Value.Make

let ($) it at = {it; at}
(* il_of_* 함수는 il.value를 반환해야 한다. *)

let default_table_max = 4294967295L
let default_memory_max = 65536L

type layout = { width : int; exponent : int; mantissa : int }
let layout32 = { width = 32; exponent = 8; mantissa = 23 }
let layout64 = { width = 64; exponent = 11; mantissa = 52 }

let mask_sign layout = Z.shift_left Z.one (layout.width - 1)
let mask_mag layout = Z.pred (mask_sign layout)
let mask_mant layout = Z.(pred (shift_left one layout.mantissa))
let mask_exp layout = Z.(mask_mag layout - mask_mant layout)
let bias layout = let em1 = layout.exponent - 1 in Z.((one + one)**em1 - one)

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

let bigint_of_z_int z =
  Bigint.of_zarith_bigint z

let bigint_of_nat32 i32 =
  Z.of_int32_unsigned i32 |> bigint_of_z_nat

let bigint_of_nat64 i64 =
  Z.of_int64_unsigned i64 |> bigint_of_z_nat

let bigint_of_nat i = Z.of_int i |> bigint_of_z_nat

let il_of_fmagN layout i =
  let n = Z.logand i (mask_exp layout) in
  let m = Z.logand i (mask_mant layout) in
  let mag = if layout.width = 32 then "f32mag" else "f64mag" in
  if n = Z.zero then
    [ Term "SUBNORM"; NT (Value.nat (bigint_of_z_nat m)) ] #@ mag
  else if n <> mask_exp layout then
    [ Term "NORM"; NT (Value.nat (bigint_of_z_nat m)); NT (Value.int (bigint_of_z_int Z.(shift_right n layout.mantissa - bias layout))) ] #@ mag
  else if m = Z.zero then
    [ Term "INF" ] #@ mag
  else
    [ Term "NAN"; NT (Value.nat (bigint_of_z_nat m)) ] #@ mag

let il_of_floatN layout i =
  let i' = Z.logand i (mask_mag layout) in
  let symbols = [ if i' = i then Term "POS" else Term "NEG"; NT (il_of_fmagN layout i) ] in
  symbols #@ "f32"

let e64 = Z.(shift_left one 64)

let vec128_to_z vec =
  match V128.I64x2.to_lanes vec with
  | [ v1; v2 ] -> Z.(of_int64_unsigned v1 + e64 * of_int64_unsigned v2)
  | _ -> assert false

let il_of_float32 f32 = F32.to_bits f32 |> Z.of_int32_unsigned |> il_of_floatN layout32

let il_of_float64 f64 = F64.to_bits f64 |> Z.of_int64_unsigned |> il_of_floatN layout64

let il_of_vec128 vec = vec128_to_z vec |> bigint_of_z_nat |> Value.nat
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

let rename_i_to_f s =
  if String.length s > 0 && s.[0] = 'i' then
    "f" ^ String.sub s 1 (String.length s - 1)
  else
    s

and rename_f_to_i s =
  if String.length s > 0 && s.[0] = 'f' then
    "i" ^ String.sub s 1 (String.length s - 1)
  else
    s

let il_of_op f1 f2 = function
  | I32 op ->
    let open Common.Source in
    let v = f1 op in
    let iid = id_of_case_v v in
    let fid = rename_i_to_f iid in
    let id = var_t' "op" [ (var_t iid) $ no_region; (var_t iid) $ no_region; (var_t fid) $ no_region; (var_t fid) $ no_region ] in
    let symbols = [ Term "I32"; NT v ] in
    symbols |> case_v |> Value.make_val id
  | I64 op ->
    let open Common.Source in
    let v = f1 op in
    let iid = id_of_case_v v in
    let fid = rename_i_to_f iid in
    let id = var_t' "op" [ (var_t iid) $ no_region; (var_t iid) $ no_region; (var_t fid) $ no_region; (var_t fid) $ no_region ] in
    let symbols = [ Term "I64"; NT v ] in
    symbols |> case_v |> Value.make_val id
  | F32 op ->
    let open Common.Source in
    let v = f2 op in
    let fid = id_of_case_v v in
    let iid = rename_f_to_i fid in
    let id = var_t' "op" [ (var_t iid) $ no_region; (var_t iid) $ no_region; (var_t fid) $ no_region; (var_t fid) $ no_region ] in
    let symbols = [ Term "F32"; NT v ] in
    symbols |> case_v |> Value.make_val id
  | F64 op ->
    let open Common.Source in
    let v = f2 op in
    let fid = id_of_case_v v in
    let iid = rename_f_to_i fid in
    let id = var_t' "op" [ (var_t iid) $ no_region; (var_t iid) $ no_region; (var_t fid) $ no_region; (var_t fid) $ no_region ] in
    let symbols = [ Term "F64"; NT v ] in
    symbols |> case_v |> Value.make_val id

let il_of_int_unop = function
  | IntOp.Clz -> [ Term "Clz" ] #@ "iunop"
  | IntOp.Ctz -> [ Term "Ctz" ] #@ "iunop"
  | IntOp.Popcnt -> [ Term "Popcnt" ] #@ "iunop"
  | IntOp.ExtendS pt -> [ Term "ExtendS"; NT (il_of_pack_type pt) ] #@ "iunop"

let il_of_float_unop = function
  | FloatOp.Neg -> [ Term "Neg" ] #@ "funop"
  | FloatOp.Abs -> [ Term "Abs" ] #@ "funop"
  | FloatOp.Ceil -> [ Term "Ceil" ] #@ "funop"
  | FloatOp.Floor -> [ Term "Floor" ] #@ "funop"
  | FloatOp.Trunc -> [ Term "Trunc" ] #@ "funop"
  | FloatOp.Nearest -> [ Term "Nearest" ] #@ "funop"
  | FloatOp.Sqrt -> [ Term "Sqrt" ] #@ "funop"

let il_of_unop = il_of_op il_of_int_unop il_of_float_unop

let il_of_int_binop ibinop =
  [ Term (string_of_int_binop ibinop) ] #@ "ibinop"

let il_of_float_binop fbinop =
  [ Term (string_of_float_binop fbinop) ] #@ "fbinop"

let il_of_binop = il_of_op il_of_int_binop il_of_float_binop

let il_of_int_testop : IntOp.testop -> Value.t = function
  | IntOp.Eqz -> [ Term "Eqz" ] #@ "itestop"

let il_of_float_testop : FloatOp.testop -> Value.t = function
  | _ -> .

let il_of_testop = il_of_op il_of_int_testop il_of_float_testop

let il_of_int_relop = function
  | IntOp.Eq -> [ Term "Eq" ] #@ "irelop"
  | IntOp.Ne -> [ Term "Ne" ] #@ "irelop"
  | IntOp.LtS -> [ Term "LtS" ] #@ "irelop"
  | IntOp.LtU -> [ Term "LtU" ] #@ "irelop"
  | IntOp.GtS -> [ Term "GtS" ] #@ "irelop"
  | IntOp.GtU -> [ Term "GtU" ] #@ "irelop"
  | IntOp.LeS -> [ Term "LeS" ] #@ "irelop"
  | IntOp.LeU -> [ Term "LeU" ] #@ "irelop"
  | IntOp.GeS -> [ Term "GeS" ] #@ "irelop"
  | IntOp.GeU -> [ Term "GeU" ] #@ "irelop"

let il_of_float_relop = function
  | FloatOp.Eq -> [ Term "Eq" ] #@ "frelop"
  | FloatOp.Ne -> [ Term "Ne" ] #@ "frelop"
  | FloatOp.Lt -> [ Term "Lt" ] #@ "frelop"
  | FloatOp.Gt -> [ Term "Gt" ] #@ "frelop"
  | FloatOp.Le -> [ Term "Le" ] #@ "frelop"
  | FloatOp.Ge -> [ Term "Ge" ] #@ "frelop"

let il_of_relop = il_of_op il_of_int_relop il_of_float_relop

let il_of_int_cvtop = function
  | IntOp.ExtendSI32 -> [ Term "ExtendSI32" ] #@ "icvtop"
  | IntOp.ExtendUI32 -> [ Term "ExtendUI32" ] #@ "icvtop"
  | IntOp.WrapI64 -> [ Term "WrapI64" ] #@ "icvtop"
  | IntOp.TruncSF32 -> [ Term "TruncSF32" ] #@ "icvtop"
  | IntOp.TruncUF32 -> [ Term "TruncUF32" ] #@ "icvtop"
  | IntOp.TruncSF64 -> [ Term "TruncSF64" ] #@ "icvtop"
  | IntOp.TruncUF64 -> [ Term "TruncUF64" ] #@ "icvtop"
  | IntOp.TruncSatSF32 -> [ Term "TruncSatSF32" ] #@ "icvtop"
  | IntOp.TruncSatUF32 -> [ Term "TruncSatUF32" ] #@ "icvtop"
  | IntOp.TruncSatSF64 -> [ Term "TruncSatSF64" ] #@ "icvtop"
  | IntOp.TruncSatUF64 -> [ Term "TruncSatUF64" ] #@ "icvtop"
  | IntOp.ReinterpretFloat -> [ Term "ReinterpretFloat" ] #@ "icvtop"

let il_of_float_cvtop = function
  | FloatOp.ConvertSI32 -> [ Term "ConvertSI32" ] #@ "fcvtop"
  | FloatOp.ConvertUI32 -> [ Term "ConvertUI32" ] #@ "fcvtop"
  | FloatOp.ConvertSI64 -> [ Term "ConvertSI64" ] #@ "fcvtop"
  | FloatOp.ConvertUI64 -> [ Term "ConvertUI64" ] #@ "fcvtop"
  | FloatOp.PromoteF32 -> [ Term "PromoteF32" ] #@ "fcvtop"
  | FloatOp.DemoteF64 -> [ Term "DemoteF64" ] #@ "fcvtop"
  | FloatOp.ReinterpretInt -> [ Term "ReinterpretInt" ] #@ "fcvtop"

let il_of_cvtop = il_of_op il_of_int_cvtop il_of_float_cvtop

let il_of_num = function
  | I32 i32 -> [ Term "I32"; NT (Value.nat (bigint_of_nat32 i32)) ] #@ "num_"
  | I64 i64 -> [ Term "I64"; NT (Value.nat (bigint_of_nat64 i64)) ] #@ "num_"
  | F32 f32 -> [ Term "F32"; NT (il_of_float32 f32) ] #@ "num_"
  | F64 f64 -> [ Term "F64"; NT (il_of_float64 f64) ] #@ "num_"

let vec_rename_i_to_f s =
  if String.length s > 0 && s.[1] = 'i' then
    "vf" ^ String.sub s 2 (String.length s - 2)
  else
    s

let vec_op_name s =
  if String.length s > 0 then
    "v" ^ String.sub s 2 (String.length s - 2)
  else
    s

let il_of_vop ?(vflag=false) f1 f2 = function
  | V128 vop -> (
    let open Common.Source in
    match vop with
    | V128.I8x16 op ->
      let v = f1 op in
      let iid = id_of_case_v v in
      let ftarg = if vflag then (var_t "void") $ no_region else (var_t (vec_rename_i_to_f iid)) $ no_region in
      let opname = vec_op_name iid in
      let id = var_t' opname [ (var_t iid) $ no_region; (var_t iid) $ no_region; (var_t iid) $ no_region; (var_t iid) $ no_region; ftarg; ftarg ] in
      let v2 = [ Term "I8x16"; NT v ]  |> case_v |> Value.make_val id in
      [ Term "V128"; NT v2 ] #@ (opname ^ "_")
    | V128.I16x8 op ->
      let v = f1 op in
      let iid = id_of_case_v v in
      let ftarg = if vflag then (var_t "void") $ no_region else (var_t (vec_rename_i_to_f iid)) $ no_region in
      let opname = vec_op_name iid in
      let id = var_t' opname [ (var_t iid) $ no_region; (var_t iid) $ no_region; (var_t iid) $ no_region; (var_t iid) $ no_region; ftarg; ftarg ] in
      let v2 = [ Term "I16x8"; NT v ]  |> case_v |> Value.make_val id in
      [ Term "V128"; NT v2 ] #@ (opname ^ "_")
    | V128.I32x4 op ->
      let v = f1 op in
      let iid = id_of_case_v v in
      let ftarg = if vflag then (var_t "void") $ no_region else (var_t (vec_rename_i_to_f iid)) $ no_region in
      let opname = vec_op_name iid in
      let id = var_t' opname [ (var_t iid) $ no_region; (var_t iid) $ no_region; (var_t iid) $ no_region; (var_t iid) $ no_region; ftarg; ftarg ] in
      let v2 = [ Term "I32x4"; NT v ]  |> case_v |> Value.make_val id in
      [ Term "V128"; NT v2 ] #@ (opname ^ "_")
    | V128.I64x2 op ->
      let v = f1 op in
      let iid = id_of_case_v v in
      let ftarg = if vflag then (var_t "void") $ no_region else (var_t (vec_rename_i_to_f iid)) $ no_region in
      let opname = vec_op_name iid in
      let id = var_t' opname [ (var_t iid) $ no_region; (var_t iid) $ no_region; (var_t iid) $ no_region; (var_t iid) $ no_region; ftarg; ftarg ] in
      let v2 = [ Term "I64x2"; NT v ]  |> case_v |> Value.make_val id in
      [ Term "V128"; NT v2 ] #@ (opname ^ "_")
    | V128.F32x4 op ->
      let v = f2 op in
      let iid = id_of_case_v v in
      let ftarg = if vflag then (var_t "void") $ no_region else (var_t (vec_rename_i_to_f iid)) $ no_region in
      let opname = vec_op_name iid in
      let id = var_t' opname [ (var_t iid) $ no_region; (var_t iid) $ no_region; (var_t iid) $ no_region; (var_t iid) $ no_region; ftarg; ftarg ] in
      let v2 = [ Term "F32x4"; NT v ]  |> case_v |> Value.make_val id in
      [ Term "V128"; NT v2 ] #@ (opname ^ "_")
    | V128.F64x2 op ->
      let v = f2 op in
      let iid = id_of_case_v v in
      let ftarg = if vflag then (var_t "void") $ no_region else (var_t (vec_rename_i_to_f iid)) $ no_region in
      let opname = vec_op_name iid in
      let id = var_t' opname [ (var_t iid) $ no_region; (var_t iid) $ no_region; (var_t iid) $ no_region; (var_t iid) $ no_region; ftarg; ftarg ] in
      let v2 = [ Term "F64x2"; NT v ]  |> case_v |> Value.make_val id in
      [ Term "V128"; NT v2 ] #@ (opname ^ "_")
  )

let il_of_int_vtestop : V128Op.itestop -> Value.t = function
  | V128Op.AllTrue -> [ Term "AllTrue" ] #@ "vitestop"

let il_of_float_vtestop : Ast.void -> Value.t = function
  | _ -> .

let il_of_vtestop = il_of_vop il_of_int_vtestop il_of_float_vtestop

let il_of_int_vrelop : V128Op.irelop -> Value.t = function
  | V128Op.Eq -> [ Term "Eq" ] #@ "virelop"
  | V128Op.Ne ->  [ Term "Ne" ] #@ "virelop"
  | V128Op.LtS -> [ Term "LtS" ] #@ "virelop"
  | V128Op.LtU -> [ Term "LtU" ] #@ "virelop"
  | V128Op.LeS -> [ Term "LeS" ] #@ "virelop"
  | V128Op.LeU -> [ Term "LeU" ] #@ "virelop"
  | V128Op.GtS -> [ Term "GtS" ] #@ "virelop"
  | V128Op.GtU -> [ Term "GtU" ] #@ "virelop"
  | V128Op.GeS -> [ Term "GeS" ] #@ "virelop"
  | V128Op.GeU -> [ Term "GeU" ] #@ "virelop"

let il_of_float_vrelop : V128Op.frelop -> Value.t = function
  | V128Op.Eq -> [ Term "Eq" ] #@ "vfrelop"
  | V128Op.Ne -> [ Term "Ne" ] #@ "vfrelop"
  | V128Op.Lt -> [ Term "Lt" ] #@ "vfrelop"
  | V128Op.Le -> [ Term "Le" ] #@ "vfrelop"
  | V128Op.Gt -> [ Term "Gt" ] #@ "vfrelop"
  | V128Op.Ge -> [ Term "Ge" ] #@ "vfrelop"

let il_of_vrelop = il_of_vop il_of_int_vrelop il_of_float_vrelop

let il_of_vec = function
  | V128 v128 ->
    let symbols = [ Term "V128"; NT (il_of_vec128 v128) ] in
    symbols #@ "vec_"

let il_of_int_vunop : V128Op.iunop -> Value.t = function
  | V128Op.Abs -> [ Term "Abs" ] #@ "viunop"
  | V128Op.Neg -> [ Term "Neg" ] #@ "viunop"
  | V128Op.Popcnt -> [ Term "Popcnt" ] #@ "viunop"

let il_of_float_vunop : V128Op.funop -> Value.t = function
  | V128Op.Abs -> [ Term "Abs" ] #@ "vfunop"
  | V128Op.Neg -> [ Term "Neg" ] #@ "vfunop"
  | V128Op.Sqrt -> [ Term "Sqrt" ] #@ "vfunop"
  | V128Op.Ceil -> [ Term "Ceil" ] #@ "vfunop"
  | V128Op.Floor -> [ Term "Floor" ] #@ "vfunop"
  | V128Op.Trunc -> [ Term "Trunc" ] #@ "vfunop"
  | V128Op.Nearest -> [ Term "Nearest" ] #@ "vfunop"

let il_of_vunop = il_of_vop il_of_int_vunop il_of_float_vunop

let il_of_int_vbinop : V128Op.ibinop -> Value.t = function
  | V128Op.Add -> [ Term "Add" ] #@ "vibinop"
  | V128Op.Sub -> [ Term "Sub" ] #@ "vibinop"
  | V128Op.Mul -> [ Term "Mul" ] #@ "vibinop"
  | V128Op.MinS -> [ Term "MinS" ] #@ "vibinop"
  | V128Op.MinU -> [ Term "MinU" ] #@ "vibinop"
  | V128Op.MaxS -> [ Term "MaxS" ] #@ "vibinop"
  | V128Op.MaxU -> [ Term "MaxU" ] #@ "vibinop"
  | V128Op.AvgrU -> [ Term "AvgrU" ] #@ "vibinop"
  | V128Op.AddSatS -> [ Term "AddSatS" ] #@ "vibinop"
  | V128Op.AddSatU -> [ Term "AddSatU" ] #@ "vibinop"
  | V128Op.SubSatS -> [ Term "SubSatS" ] #@ "vibinop"
  | V128Op.SubSatU -> [ Term "SubSatU" ] #@ "vibinop"
  | V128Op.DotS -> [ Term "DotS" ] #@ "vibinop"
  | V128Op.Q15MulRSatS -> [ Term "Q15MulRSatS" ] #@ "vibinop"
  | V128Op.ExtMulLowS -> [ Term "ExtMulLowS" ] #@ "vibinop"
  | V128Op.ExtMulHighS -> [ Term "ExtMulHighS" ] #@ "vibinop"
  | V128Op.ExtMulLowU -> [ Term "ExtMulLowU" ] #@ "vibinop"
  | V128Op.ExtMulHighU -> [ Term "ExtMulHighU" ] #@ "vibinop"
  | V128Op.Swizzle -> [ Term "Swizzle" ] #@ "vibinop"
  | V128Op.Shuffle l ->
    let intv_list = List.map (fun i -> Value.nat (bigint_of_nat i)) l in
    let symbols = [ Term "Shuffle"; NT (Make.list (Il.Typ.nat) intv_list) ] in
    symbols #@ "vibinop"
  | V128Op.NarrowS -> [ Term "NarrowS" ] #@ "vibinop"
  | V128Op.NarrowU -> [ Term "NarrowU" ] #@ "vibinop"
  | V128Op.RelaxedSwizzle -> [ Term "RelaxedSwizzle" ] #@ "vibinop"
  | V128Op.RelaxedQ15MulRS ->  [ Term "RelaxedQ15MulRS" ] #@ "vibinop"
  | V128Op.RelaxedDot -> [ Term "RelaxedDot" ] #@ "vibinop"

let il_of_float_vbinop : V128Op.fbinop -> Value.t = function
  | V128Op.Add -> [ Term "Add" ] #@ "vfbinop"
  | V128Op.Sub -> [ Term "Sub" ] #@ "vfbinop"
  | V128Op.Mul -> [ Term "Mul" ] #@ "vfbinop"
  | V128Op.Div -> [ Term "Div" ] #@ "vfbinop"
  | V128Op.Min -> [ Term "Min" ] #@ "vfbinop"
  | V128Op.Max -> [ Term "Max" ] #@ "vfbinop"
  | V128Op.Pmin -> [ Term "Pmin" ] #@ "vfbinop"
  | V128Op.Pmax -> [ Term "Pmax" ] #@ "vfbinop"
  | V128Op.RelaxedMin -> [ Term "RelaxedMin" ] #@ "vfbinop"
  | V128Op.RelaxedMax -> [ Term "RelaxedMax" ] #@ "vfbinop"

let il_of_vbinop = il_of_vop il_of_int_vbinop il_of_float_vbinop

let il_of_instr instr =
  match instr.it with
  | LocalGet idx ->
    let symbols = [ Term "LOCAL.GET"; NT (il_of_idx "localidx" (idx.it $ no_region)) ] in
    symbols #@ "instr"
  | LocalSet idx ->
    let symbols = [ Term "LOCAL.SET"; NT (il_of_idx "localidx" (idx.it $ no_region)) ] in
    symbols #@ "instr"
  | LocalTee idx ->
    let symbols = [ Term "LOCAL.TEE"; NT (il_of_idx "localidx" (idx.it $ no_region)) ] in
    symbols #@ "instr"
  | GlobalGet idx ->
    let symbols = [ Term "GLOBAL.GET"; NT (il_of_idx "globalidx" (idx.it $ no_region)) ] in
    symbols #@ "instr"
  | GlobalSet idx ->
    let symbols = [ Term "GLOBAL.SET"; NT (il_of_idx "globalidx" (idx.it $ no_region)) ] in
    symbols #@ "instr"
  | TableGet idx ->
    let symbols = [ Term "TABLE.GET"; NT (il_of_idx "tableidx" (idx.it $ no_region)) ] in
    symbols #@ "instr"
  | TableSet idx ->
    let symbols = [ Term "TABLE.SET"; NT (il_of_idx "tableidx" (idx.it $ no_region)) ] in
    symbols #@ "instr"
  | TableSize idx ->
    let symbols = [ Term "TABLE.SIZE"; NT (il_of_idx "tableidx" (idx.it $ no_region)) ] in
    symbols #@ "instr"
  | TableGrow idx ->
    let symbols = [ Term "TABLE.GROW"; NT (il_of_idx "tableidx" (idx.it $ no_region)) ] in
    symbols #@ "instr"
  | TableFill idx ->
    let symbols = [ Term "TABLE.FILL"; NT (il_of_idx "tableidx" (idx.it $ no_region)) ] in
    symbols #@ "instr"
  | TableCopy (idx1, idx2) ->
    let symbols = [ Term "TABLE.COPY"; NT (il_of_idx "tableidx" (idx1.it $ no_region)); NT (il_of_idx "tableidx" (idx2.it $ no_region)) ] in
    symbols #@ "instr"
  | TableInit (idx1, idx2) ->
    let symbols = [ Term "TABLE.INIT"; NT (il_of_idx "tableidx" (idx1.it $ no_region)); NT (il_of_idx "elemidx" (idx2.it $ no_region)) ] in
    symbols #@ "instr"
  | Const num ->
    let symbols = [ Term "CONST"; NT (il_of_num num.it) ] in
    symbols #@ "instr"
  | Test op ->
    let symbols = [ Term "TEST"; NT (il_of_testop op) ] in
    symbols #@ "instr"
  | Compare op ->
    let symbols = [ Term "COMPARE"; NT (il_of_relop op) ] in
    symbols #@ "instr"
  | Unary op ->
    let symbols = [ Term "UNARY"; NT (il_of_unop op) ] in
    symbols #@ "instr"
  | Binary op ->
    let symbols = [ Term "BINOP"; NT (il_of_binop op) ] in
    symbols #@ "instr"
  | Convert op ->
    let symbols = [ Term "CONVERT"; NT (il_of_cvtop op) ] in
    symbols #@ "instr"
  | VecConst vec ->
    let symbols = [ Term "VEC.CONST"; NT (il_of_vec vec.it) ] in
    symbols #@ "instr"
  | VecTest vop ->
    let symbols = [ Term "VEC.TEST"; NT (il_of_vtestop vop) ] in
    symbols #@ "instr"
  | VecUnary vop ->
    let symbols = [ Term "VEC.UNARY"; NT (il_of_vunop vop) ] in
    symbols #@ "instr"
  | VecBinary vop ->
    let symbols = [ Term "VEC.BINARY"; NT (il_of_vbinop vop) ] in
    symbols #@ "instr"
  | VecCompare vop ->
    let symbols = [ Term "VEC.COMPARE"; NT (il_of_vrelop vop) ] in
    symbols #@ "instr"
  (*
  | VecConvert vop ->
  | VecTernary vop ->
  | VecShift vop ->
  | VecBitmask vop ->
  | VecTestBits vop ->
  | VecUnaryBits vop ->
  | VecBinaryBits vop ->
  | VecTernaryBits vop ->
  | VecSplat vop ->
  | VecExtract vop ->
  | VecReplace vop -> *)
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
