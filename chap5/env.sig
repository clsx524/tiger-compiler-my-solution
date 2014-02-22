(*-------------------------------------
  This section ©1998 by Andrew W. Appel
  -------------------------------------*)

signature ENV =
sig
  type access
  type ty
  datatype enventry = VarEntry of {ty: ty}
                    | FunEntry of {formals: ty list, result: ty}
                    | NameEntry of Symbol.symbol * enventry option ref
  val base_tenv : ty Symbol.table       (* predefined types *)
  val base_venv : enventry Symbol.table (* predefined functions *)
end