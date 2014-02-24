structure Semant :
sig
   val transProg : Absyn.exp -> unit
end
=
struct
	val nestLevel = ref 0
	exception Error

	structure A = Absyn
	structure E = Env
	structure S = Symbol
	type enventrytable = Env.enventry Symbol.table
	type tytable = Types.ty Symbol.table
	structure Translate = struct type exp = unit end
	type expty = {exp: Translate.exp, sym:Symbol.symbol, ty: Types.ty}

	val tenv = Env.base_tenv
	val venv = Env.base_venv

	(*look up symbol in the type env*)
	fun lookup (tenv, symbol, pos) = case S.look(tenv, symbol) of
										 SOME t => t
      								   | NONE => (ErrorMsg.error pos ("Type is not defined: " ^ S.name(symbol));Types.BOTTOM)

    fun checkInt ({exp,sym,ty}, pos) = case ty of 
    			  Types.INT => ()
				| Types.BOTTOM => ()
				| _ => ErrorMsg.error pos "integer required"  	

	fun checkUnit ({exp,sym,ty},pos) = case ty of 
				  Types.UNIT => ()
				| Types.NIL => ()
				| Types.BOTTOM => ()
				| _ => ErrorMsg.error pos "Expression must return no value"		

	fun checkString ({exp,sym,ty} ,pos) = case ty of 
				  Types.STRING => ()
				| Types.BOTTOM => ()
				| _ => ErrorMsg.error pos "string required"	

	fun actual_ty (Types.NAME(symbol, tyOpt), pos) = (
			case !tyOpt of 
	 		SOME t => actual_ty (t, pos)
       	|   NONE => Types.NAME(symbol, tyOpt))
      | actual_ty (t, pos) = t	
      (*(ErrorMsg.error pos ("Type is not defined: " ^ Symbol.name(symbol)); Types.BOTTOM))*)

	fun eqTypes (ty1, ty2, pos) = case (ty1, ty2) of 
				  (Types.BOTTOM, _) => true
				| (_, Types.BOTTOM) => true
				| (Types.RECORD(_,u1), Types.RECORD(_,u2)) => (u1 = u2)
				| (Types.ARRAY(_,u1),Types.ARRAY(_,u2)) => 	(u1=u2)
				| (Types.NAME(_,_), Types.NAME(_,_)) => eqTypes(actual_ty (ty1, pos), actual_ty (ty2, pos), pos)
				| (Types.NAME(_,_),_) => eqTypes(actual_ty (ty1, pos), ty2, pos)
				| (_,Types.NAME(_,_)) => eqTypes(ty1, actual_ty (ty2, pos), pos)
				| (Types.RECORD(_,_), Types.NIL) => true
    			| (Types.NIL, Types.RECORD(_,_)) => true
    			| (_,_) => (ty1 = ty2)			

	(* eqTypeList: Type.ty list * Type.ty list -> bool *)
	fun eqTypeList ([], [], pos) = true
    |	eqTypeList ([], l, pos) = false
    |	eqTypeList (l, [], pos) = false
    |	eqTypeList ([ty1], [ty2], pos) = eqTypes(ty1, ty2, pos)
    |	eqTypeList (hd1::l1, hd2::l2, pos) = eqTypes(hd1, hd2, pos) andalso eqTypeList(l1, l2, pos)			

	fun transExp (venv, tenv) = let 
		fun trexp (A.VarExp v) = trvar v 												(* VarExp *)
		| 	trexp (A.NilExp) = {exp = (), sym = [], ty = Types.NIL}						(* NilExp *)
		| 	trexp (A.IntExp i) = {exp = (), sym = [], ty = Types.INT}				 	(* IntExp *)
        |	trexp (A.StringExp (s, pos)) = {exp = (), sym = [], ty = Types.STRING}		(* StringExp *)
        |	trexp (A.CallExp {func, args, pos}) = (case S.look(venv,func) of 			(* CallExp *)
        		SOME (E.FunEntry {formals, result}) => let 
					val argtys = map #ty (map trexp args)
        		in 
        			if eqTypeList(formals, argtys, pos) 
        			then {exp = (), sym = [], ty = actual_ty (result, pos)} 
        			else (ErrorMsg.error pos ((S.name func) ^" function arguments do not agree"); {exp = (), sym = [],ty=Types.BOTTOM})
        		end
        	| 	SOME (E.VarEntry{ty}) => ((ErrorMsg.error pos " undefined function"); {exp = (), sym = [], ty = Types.BOTTOM})	
        	|   SOME (E.NameEntry(name, funcname, ind)) => (case !funcname of
        		 							SOME (E.FunEntry {formals, result}) => let 
												val argtys = map #ty (map trexp args)
        									in 
        										if eqTypeList(formals, argtys, pos) 
        										then {exp = (), sym = (if !ind = false then [name] else []), ty = actual_ty (result, pos)} 
        										else (ErrorMsg.error pos ((S.name func) ^" function arguments do not agree"); {exp = (), sym = [],ty=Types.BOTTOM})
        									end
        								|   _ => (ErrorMsg.error pos ((S.name func) ^" function has not been declared or invalid enventry"); {exp = (), sym = [],ty=Types.BOTTOM}))

        	| 	NONE => (ErrorMsg.error pos " undefined function"; {exp = (), sym = [], ty = Types.BOTTOM}))

		|	trexp (A.OpExp {left, oper, right, pos}) = let					(* OpExp *)
				val left' = trexp left
				val right' = trexp right
				in 
					((case (left') of 
					{exp = _, sym = _, ty = Types.INT} => checkInt(right', pos)
				|   {exp = _, sym = _, ty = Types.STRING} => checkString(right', pos)
				|   {exp = _, sym = _, ty = Types.ARRAY(_)} => (case oper of 
						A.EqOp => (if eqTypes(#ty left', #ty right', pos) then () else ErrorMsg.error pos "type mismatch")
					|   A.NeqOp => (if eqTypes(#ty left', #ty right', pos) then () else ErrorMsg.error pos "type mismatch")
					|   _ => (ErrorMsg.error pos "operation not valid for ARRAYS"))
				| 	{exp = _, sym = _, ty = Types.RECORD(_)} => (case oper of 
						A.EqOp => (if eqTypes(#ty left', #ty right', pos) then () else ErrorMsg.error pos "type mismatch")
					|   A.NeqOp => (if eqTypes(#ty left', #ty right', pos) then () else ErrorMsg.error pos "type mismatch")
					|   _ => (ErrorMsg.error pos "operation not valid for RECORDS"))	
				| 	{exp = _, sym = _, ty=Types.NIL} =>(case oper of
						A.EqOp => (if eqTypes(#ty left', #ty right', pos) then () else ErrorMsg.error pos "type mismatch")
					|   A.NeqOp => (if eqTypes(#ty left', #ty right', pos) then () else ErrorMsg.error pos "type mismatch")
					|   _ => (ErrorMsg.error pos "operation not valid for NIL"))
				| 	{exp = _, sym = _, ty = Types.BOTTOM} => ()
				| 	_ => (ErrorMsg.error pos "invalid operation"));
					
					{exp = (), sym = [], ty = Types.INT})
				end

		| trexp (A.RecordExp {fields,typ,pos}) = let  (* RecordExp *) 
			val actualType = actual_ty (lookup (tenv, typ, pos), pos)						
        	fun findFieldType sym = let
	        	fun helper((s, ty), t) = if s = sym then ty else t
		        in 
		        	(case actualType of 
		        		Types.RECORD (l, unique) => foldl helper Types.UNIT l
		        	|   _ => (ErrorMsg.error pos "Not a record type"; Types.BOTTOM))
		        end
		        	
		    fun checkFieldTypes (sym, exp, pos) = let
		    	val t = findFieldType sym
		    	in
		    		if eqTypes(t, #ty (trexp exp), pos) then () else ErrorMsg.error pos "Mismatching field types"
		    	end 	
		    val () = app checkFieldTypes fields

        	in
        		{exp = (), sym = [], ty = actualType}
        	end

        | trexp (A.SeqExp l) = let											(* SeqExp *)
        	fun seqHelper [(exp,pos)] = trexp exp
              | seqHelper ((exp,pos)::tail) = let
              	val {exp = e , sym = s, ty = t} = trexp exp
              	val {exp = e', sym = s', ty = t'} = seqHelper tail
              in
              	{exp = e', sym = s @ s', ty = t'}
              end
              | seqHelper [] = trexp(A.NilExp)
        	in 
        		seqHelper l
        	end

        | trexp (A.AssignExp {var,exp,pos}) = let							(* AssignExp *)
        	val var_ty = #ty (trvar (var))
        	val exp_ty = #ty (trexp (exp))
        	in 
        		if (eqTypes(var_ty, exp_ty, pos)) then {exp = (), sym = [], ty = Types.UNIT}
        		else (ErrorMsg.error pos "type mismatch in var assignment";{exp = (), sym = [], ty = Types.BOTTOM})
        	end

		| trexp (A.IfExp {test, then' = thenexp, else' = NONE, pos}) =  (* IfExp *)
        	(checkInt(trexp test, pos); checkUnit(trexp thenexp, pos);
        	{exp = (), sym = [],ty = Types.UNIT})

        | trexp (A.IfExp {test, then' = thenexp, else' = SOME(elseexp), pos}) = let
        	val then_ty = #ty (trexp thenexp)
        	val else_ty = #ty (trexp elseexp)
        	in
        		(checkInt(trexp test,pos);
        		if eqTypes(then_ty, else_ty, pos) then {exp = (), sym = [], ty = then_ty}
        		else (ErrorMsg.error pos "then and else expressions must have same type"; 

        		{exp = (), sym = [], ty = then_ty}))
        	end

		| trexp (A.WhileExp {test,body,pos}) = (						(* WhileExp *)
			checkInt (trexp test, pos);	
        	nestLevel := !nestLevel + 1;
        	checkUnit (trexp body, pos);
        	nestLevel := !nestLevel - 1;	
        		 
        	{exp = (), sym = [], ty = Types.UNIT})

        | trexp (A.ForExp {var, escape, lo, hi, body, pos}) = let			(* ForExp *)
        	val () = checkInt (trexp lo, pos)
        	val () = checkInt (trexp hi, pos)
        	val venv' = S.enter(venv, var, E.VarEntry{ty = Types.INT})  (* local variable*)
        	val () = (nestLevel := !nestLevel + 1)
        	val {exp, sym, ty} = transExp (venv', tenv) body
        	val () = (nestLevel := !nestLevel - 1)
        	val () = checkUnit ({exp = exp, sym = sym, ty = ty}, pos)
        	in
        		{exp = (), sym = [], ty = ty}
        	end

        | trexp (A.BreakExp(pos)) = 									(* BreakExp *)
        	if (!nestLevel <> 0) 
        	then {exp = (), sym = [], ty = Types.UNIT}
        	else (ErrorMsg.error pos "Break must be within a loop"; {exp = (), sym = [], ty = Types.BOTTOM})

		| trexp (A.LetExp{decs, body, pos}) = let							(* LetExp *)
        	val {venv = venv', tenv = tenv'} = transDecs(venv, tenv, decs, pos)
        	in 
        		transExp(venv',tenv') body
        	end
        	
        | trexp (A.ArrayExp {typ, size, init, pos}) = let					(* ArrayExp *)
      		val {exp = _, sym = _, ty = tyinit} = trexp init;
      		in
      			checkInt(trexp size, pos);
        		case S.look(tenv, typ) of 
             		NONE   => (ErrorMsg.error pos "undeclared type"; {exp = (), sym = [], ty = Types.BOTTOM})
          		|   SOME t => (case actual_ty (t, pos) of
          		 		Types.ARRAY (ty,unique) => (
          		 		if eqTypes(tyinit, ty, pos) 
               			then {exp = (), sym = [], ty = Types.ARRAY (ty,unique) }
               			else (ErrorMsg.error pos ("Expected: " ^ Types.toString ty ^ " Actual: " ^ Types.toString tyinit); {exp = (), sym = [], ty = Types.BOTTOM}))
               			|   _      => (ErrorMsg.error pos (S.name typ ^" is not of array type"); {exp = (), sym = [], ty = Types.BOTTOM}))
           	end
           	 	
		and trvar (A.SimpleVar(id,pos)) = (
			case Symbol.look(venv, id) of 
			SOME (E.VarEntry{ty}) => {exp = (), sym = [], ty = actual_ty (ty, pos)}
	  	|   _ => (ErrorMsg.error pos ("undefined variable " ^ Symbol.name id); {exp = (), sym = [], ty = Types.BOTTOM}))

    	|   trvar (A.FieldVar(var, id, pos)) = (
    		case trvar var of 
    		{exp, sym, ty = Types.RECORD(fields,_)} => let 
             	fun idfinder (symid,_) = (symid = id)
            in (
            	case (List.find idfinder fields) of 
                SOME(_,ty) => {exp = (), sym = [], ty = actual_ty (ty, pos)}
            |   NONE       => (ErrorMsg.error pos ("record does not have this field" ^ Symbol.name id);
                              {exp = (), sym = [],ty = Types.BOTTOM}))
            end
      	|   _              => (ErrorMsg.error pos "not a record type"; {exp = (), sym = [], ty=Types.BOTTOM}))

    	|   trvar (A.SubscriptVar(var, exp, pos)) = (
    		checkInt((trexp exp), pos);
            case (#ty (trvar var)) of 
            Types.ARRAY(ty, _) => {exp = (), sym = [], ty = actual_ty (ty, pos)}
        |   Types.BOTTOM       => {exp = (), sym = [], ty = Types.BOTTOM}
        |   _                  => (ErrorMsg.error pos ("not an array type"); {exp = (), sym = [], ty=Types.BOTTOM}))
	in 
		trexp 
	end

	and transTy(tenv, A.RecordTy l) = let 
			val thisre : Symbol.symbol list ref = ref []
			fun convFieldToTuple {name,escape,typ,pos} = let
				val res = lookup(tenv,typ,pos)
				val () = case res of 
						Types.NAME(nn, rr) => (case !rr of 
											   NONE => thisre := !thisre @ [nn] 
											|  _    => thisre := !thisre) 
					|   _ => thisre := !thisre
			in
				(name, res)
			end
			val tupleList = map convFieldToTuple l
		in
			{somety = Types.RECORD(tupleList,ref ()), thisremain = !thisre}
		end

	|   transTy (tenv, A.ArrayTy(s,pos)) = let
			val thisre : Symbol.symbol list ref = ref []
			val res = lookup(tenv,s,pos)
			val r = (case res of Types.NAME(nn, rr) => rr |	_ => ref NONE)
		in
			(thisre := (case !r of
					SOME (Types.NAME(nn, rr)) => (
							if !rr <> SOME Types.INT andalso 
							   !rr <> SOME Types.STRING andalso 
							   !rr <> SOME Types.NIL andalso 
							   !rr <> SOME Types.UNIT
							then !thisre @ [nn] else !thisre)
				|	_ => !thisre);
			{somety = Types.ARRAY(res,ref ()), thisremain = !thisre})
		end

	|   transTy (tenv, A.NameTy(s,pos)) = let
		val actualType = actual_ty (lookup(tenv, s, pos), pos)
		val isValid = case actualType of
							(Types.RECORD l) => true
						| 	(Types.ARRAY(n,r)) => true
						| 	(Types.NAME(n,r)) => if n = s then true else false 
						|	_ => false
	in
		if actualType <> Types.INT andalso 
		   actualType <> Types.STRING andalso 
		   actualType <> Types.NIL andalso 
		   actualType <> Types.UNIT andalso 
		   isValid = false
		then (ErrorMsg.error pos "mutually recursive types should pass through record or array"; 
			{somety = Types.BOTTOM, thisremain = []})
		else {somety = Types.NAME(s, ref (SOME actualType)), thisremain = []}
	end

	and transDecs (venv, tenv, l, pos) = let
		val emptyList : A.symbol list = []
		val {venv = v, tenv = t} = (foldl transDecName {venv=venv, tenv=tenv} l)
		val {venv = v', tenv = t', remains = re', prev = p'} = (foldl transDec {venv = v, tenv = t, remains = emptyList, prev = (Symbol.symbol "0")} l)
		fun hasNonVarDec(item) = 
			case S.look(venv, item) of
			SOME (E.NameEntry(n,r,f)) => (ErrorMsg.error pos "Definition of recursive functions is interrupted")
		|	SOME (E.VarEntry{ty}) => ()
		|	_ => (ErrorMsg.error pos ("Definition of recursive types is interrupted "^(Symbol.name item)))

		val () = (app hasNonVarDec re')
	in
		{venv = v', tenv = t'}
	end

	and transDecName (A.VarDec l, {venv, tenv}) = {venv = venv, tenv = tenv}
	|   transDecName (A.TypeDec l, {venv, tenv}) = let
		fun addHeaders (name,tenv) = (S.enter (tenv, name, Types.NAME(name, ref NONE)))
		val tenv' = foldl addHeaders tenv (map #name l)
	in
		{venv = venv, tenv = tenv'}
	end
	|   transDecName (A.FunctionDec l, {venv, tenv}) = let
		fun getResultType (SOME(rt,pos)) = (case S.look(tenv,rt) of 
											SOME(t) => t
										|   NONE => (ErrorMsg.error pos "Return type not valid"; Types.BOTTOM))
		|   getResultType NONE = Types.UNIT
					
		fun transparam{name, escape, typ, pos} = case S.look(tenv,typ) of 
											  	 SOME t => {name=name,ty=t}
								             |   NONE => (ErrorMsg.error pos ((S.name typ)^" undefined type"); 
								             	          {name = name, ty = Types.UNIT})
		fun addHeaders ({name, params, result, body, pos}, venv) = let 
			val result_ty = getResultType result
			val params' = map transparam params
			in 
				S.enter(venv, name, E.NameEntry(name, ref (SOME (E.FunEntry{formals = map #ty params', result = result_ty})), ref false))
			end

		val venv' = foldl addHeaders venv l
	in
		{venv = venv', tenv = tenv}
	end

	and transDec (A.VarDec{name, escape, typ = NONE, init, pos}, {venv, tenv, remains, prev}) = let 
		fun hasNonVarDec(item) = 
			case S.look(venv, item) of
			SOME (E.NameEntry(n,r,f)) => (ErrorMsg.error pos "Definition of recursive functions is interrupted")
		|	SOME (E.VarEntry{ty}) => ()
		|	_ => (ErrorMsg.error pos "Definition of recursive types is interrupted")

		val () = (app hasNonVarDec remains)

		val {exp, sym, ty} = transExp(venv, tenv) init
		in 
			if ty = Types.NIL 
			then (ErrorMsg.error pos ("variable does not have a valid type " ^ (Symbol.name name)); 
				{tenv = tenv, venv = venv, remains = remains, prev = prev})
			else {tenv = tenv, venv = S.enter(venv, name, E.VarEntry{ty = ty}), remains = remains, prev = name}
		end

	|	transDec (A.VarDec{name, escape, typ = SOME (symbol, pos), init, pos = varpos}, {venv, tenv, remains, prev}) = let
		fun hasNonVarDec(item) = 
			case S.look(venv, item) of
			SOME (E.NameEntry(n,r,f)) => (ErrorMsg.error pos "Definition of recursive functions is interrupted")
		|	SOME (E.VarEntry{ty}) => ()
		|	_ => (ErrorMsg.error pos ("Definition of recursive types is interrupted "^(Symbol.name item)))

		val () = (app hasNonVarDec remains)

		val {exp, sym, ty} = transExp(venv,tenv) init
		val ty2 = actual_ty (lookup (tenv,symbol,pos), pos)		
		in 
			if eqTypes(ty, ty2, pos)
			then {tenv = tenv, venv = S.enter(venv, name, E.VarEntry{ty = ty2}), remains = remains, prev = prev}
			else (ErrorMsg.error pos "Mismatching types"; {tenv = tenv, venv = S.enter(venv, name, E.VarEntry{ty = ty}), remains = remains, prev = name})
		end

	|	transDec (A.TypeDec l, {venv, tenv, remains, prev}) = let
		val typeName = (#name (List.nth (l,0)))
		
		val () = if prev = typeName  
				 then (ErrorMsg.error (#pos (List.nth (l,0))) "two types with the same name declared consecutively.") else ()

		fun replace(Types.NAME(n,r), ty) = r := SOME ty
		  | replace(_, _) = raise Fail("not TypeDec")  

		fun replaceHeaders ({name,ty,pos}, syms) = let 
			val {somety = sty, thisremain = temp} = transTy(tenv, ty)
			val () = (case sty of
				(Types.NAME(n, r)) => (if n = typeName 
										then ErrorMsg.error pos "mutually recursive types should pass through record or array"
										else ())
			|	_ => ())

			val thisre = List.filter (fn x => x <> name) temp
			val () = replace(Option.valOf(S.look (tenv, name)), sty)
		in
			if (List.exists (fn x => x = name) syms) andalso thisre = [] 
			then List.filter (fn x => x <> name) (thisre @ syms)
			else thisre @ syms
		end

		val tr = foldl replaceHeaders remains l (*return remaining list*)
		in

			{venv = venv, tenv = tenv, remains = tr, prev = (#name (List.last l))}
	    end

	| 	transDec (A.FunctionDec l, {venv,tenv,remains,prev}) = let 
		fun hasTypeDec(item) = (
			case S.look(tenv, item) of 
			SOME (Types.NAME(n,r)) => (ErrorMsg.error (#pos (List.nth (l,0))) "mutual recursive types should be declared consecutively")
		|	_ => ())

		val () = app hasTypeDec remains

		fun getResultType (SOME(rt,pos)) = (
				case S.look(tenv,rt) of 
				SOME(t)=> t
			|   NONE => (ErrorMsg.error pos "Return type not valid";Types.BOTTOM))
		|   getResultType NONE = Types.UNIT
					
		fun transparam{name,escape,typ,pos} = case S.look(tenv,typ) of 
											  SOME t => {name=name,ty=t}
								            | NONE => (ErrorMsg.error pos ((S.name typ)^" undefined type"); {name=name,ty=Types.UNIT})

		fun processBodies ({name,params,result,body,pos}, syms) = let
			val () = case S.look(venv, name) of
				SOME (Env.NameEntry(s, r, f)) => (
					case !f of 
				 		false => f := true 
				 	|   true => if prev = name
				 				then ErrorMsg.error pos ("duplicate declaration of function "^ (Symbol.name name))
				 				else ())
			|	_ => raise Error

			val result_ty = getResultType result
			val params' = map transparam params
			fun enterparam ({name, ty}, venv) = S.enter(venv,name,E.VarEntry{ty=ty})
			val venv' = foldl enterparam venv params' 
			val {exp, sym = mutualList, ty} = transExp(venv',tenv) body
			in
				(if eqTypes(ty,result_ty, pos) 
					then () 
					else (
						ErrorMsg.error pos "function does not evaluate to correct type"); 
				 		List.filter (fn x => x <> name) (syms @ mutualList))
			end

			val thisre = foldl processBodies remains l
		in 
			{venv = venv, tenv = tenv, remains = thisre, prev = (#name (List.last l))}
		end

  	fun transProg ast = let 
		val {exp = result, sym = _, ty = _ } = transExp (E.base_venv, E.base_tenv) ast
	in 
		result
	end
end