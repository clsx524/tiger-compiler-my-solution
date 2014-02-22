structure Types =
struct

  	type unique = unit ref

  	datatype ty = RECORD of (Symbol.symbol * ty) list * unique
          	  	| NIL
          		| INT
          		| STRING
          		| ARRAY of ty * unique
	  	  		| NAME of Symbol.symbol * ty option ref
	  	  		| UNIT
	  	  		| BOTTOM

	fun toString (RECORD l) = "RECORD"
  	| toString (NIL) = "NIL"
  	| toString (INT) = "INT"
  	| toString (STRING) = "STRING"
  	| toString (ARRAY (t,u)) = "ARRAY OF " ^ (toString t)
  	| toString (UNIT) = "UNIT"
  	| toString (BOTTOM) = "BOTTOM"
  	| toString (NAME (t, r)) = "NAME"
 
end

