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
	type expty = {exp: Translate.exp, ty: Types.ty}

	val tenv = Env.base_tenv
	val venv = Env.base_venv

	(*look up symbol in the type env*)
	fun lookup (tenv, symbol, pos) = case S.look(tenv, symbol) of
										 SOME t => t
      								   | NONE => (ErrorMsg.error pos ("Type is not defined: " ^ Symbol.name(symbol));Types.BOTTOM)
	(*(ErrorMsg.error pos ("Type is not defined: " ^ Symbol.name(symbol));*)
    fun checkInt ({exp,ty}, pos) = case ty of 
    			  Types.INT => ()
				| Types.BOTTOM => ()
				| _ => ErrorMsg.error pos "integer required"  								   
	fun checkUnit ({exp,ty},pos) = case ty of 
				  Types.UNIT => ()
				| Types.NIL => ()
				| Types.BOTTOM => ()
				| _ => ErrorMsg.error pos "Expression must return no value"		
	fun checkString ({exp,ty} ,pos) = case ty of 
				  Types.STRING => ()
				| Types.BOTTOM => ()
				| _ => ErrorMsg.error pos "string required"	
	fun actual_ty (Types.NAME(symbol, tyOpt)) = (case !tyOpt of 
	 											SOME t => actual_ty t
       										  | NONE => raise Error)
      | actual_ty t = t	

	fun eqTypes (ty1,ty2) = case (ty1,ty2) of 
				  (Types.BOTTOM, _) => true
				| (_, Types.BOTTOM) => true
				| (Types.RECORD(_,u1), Types.RECORD(_,u2)) => (u1 = u2)
				| (Types.ARRAY(_,u1),Types.ARRAY(_,u2)) => 	(u1=u2)
				| (Types.NAME(_,_), Types.NAME(_,_)) => eqTypes(actual_ty ty1, actual_ty ty2)
				| (Types.NAME(_,_),_) => eqTypes(actual_ty ty1,ty2)
				| (_,Types.NAME(_,_)) => eqTypes(ty1, actual_ty ty2)
				| (Types.RECORD(_,_), Types.NIL) => true
    			| (Types.NIL, Types.RECORD(_,_)) => true
    			| (_,_) => (ty1 = ty2)			
	(* eqTypeList: Type.ty list * Type.ty list -> bool *)
	fun eqTypeList ([],[]) = true
       |eqTypeList([],l) = false
       |eqTypeList(l,[]) = false
       |eqTypeList ([ty1],[ty2]) = eqTypes(ty1,ty2)
       |eqTypeList (hd1::l1, hd2::l2) = eqTypes(hd1,hd2) andalso eqTypeList(l1,l2)			

	fun transExp (venv, tenv) = let 
		fun trexp (A.VarExp v) = trvar v 											(* VarExp *)
		| 	trexp (A.NilExp) = {exp = (), ty = Types.NIL}							(* NilExp *)
		| 	trexp (A.IntExp i) = {exp = (), ty = Types.INT}							(* IntExp *)
        |	trexp (A.StringExp (s, pos)) = {exp = (), ty = Types.STRING}			(* StringExp *)
        |	trexp (A.CallExp {func, args, pos}) = (case S.look(venv,func) of 	(* CallExp *)
        		SOME (E.FunEntry {formals, result}) => let 
					val argtys = map #ty (map trexp args)
        		in 
        			if eqTypeList(formals, argtys) 
        			then {exp = (), ty = actual_ty result} 
        			else (ErrorMsg.error pos ((S.name func) ^" function arguments do not agree"); {exp=(),ty=Types.BOTTOM})
        		end
        	| 	SOME (E.VarEntry{ty}) => ((ErrorMsg.error pos " undefined function"); {exp = (), ty = Types.BOTTOM})	
        	|   SOME (E.NameEntry(name, funcname)) => (case !funcname of
        		 							SOME (E.FunEntry {formals, result}) => let 
												val argtys = map #ty (map trexp args)
												val c = (map (fn s => print ((S.name func) ^ "c:" ^ (Types.toString s) ^ "\n")) argtys)
												val d = (map (fn s => print ((S.name func) ^ "d:" ^ (Types.toString s) ^ "\n")) formals)
        									in 
        										if eqTypeList(formals, argtys) 
        										then {exp = (), ty = actual_ty result} 
        										else (ErrorMsg.error pos ((S.name func) ^" function arguments do not agree"); {exp=(),ty=Types.BOTTOM})
        									end
        									| _ => (ErrorMsg.error pos ((S.name func) ^" function has not been declared or invalid enventry"); {exp=(),ty=Types.BOTTOM}))

        	| 	NONE => (ErrorMsg.error pos " undefined function"; {exp = (), ty = Types.BOTTOM}))

		|	trexp (A.OpExp {left, oper, right, pos}) = let					(* OpExp *)
				val left' = trexp left
				val right' = trexp right
				in 
					((case (left') of 
					{exp = _, ty = Types.INT} => checkInt(right', pos)
				|   {exp = _, ty = Types.STRING} => checkString(right', pos)
				|   {exp = _, ty = Types.ARRAY(_)} => (case oper of 
						A.EqOp => (if eqTypes(#ty left', #ty right') then () else ErrorMsg.error pos "type mismatch")
					|   A.NeqOp => (if eqTypes(#ty left', #ty right') then () else ErrorMsg.error pos "type mismatch")
					|   _ => (ErrorMsg.error pos "operation not valid for ARRAYS"))
				| 	{exp = _, ty = Types.RECORD(_)} => (case oper of 
						A.EqOp => (if eqTypes(#ty left', #ty right') then () else ErrorMsg.error pos "type mismatch")
					|   A.NeqOp => (if eqTypes(#ty left', #ty right') then () else ErrorMsg.error pos "type mismatch")
					|   _ => (ErrorMsg.error pos "operation not valid for RECORDS"))	
				| 	{exp=_,ty=Types.NIL} =>(case oper of
						A.EqOp => (if eqTypes(#ty left', #ty right') then () else ErrorMsg.error pos "type mismatch")
					|   A.NeqOp => (if eqTypes(#ty left', #ty right') then () else ErrorMsg.error pos "type mismatch")
					|   _ => (ErrorMsg.error pos "operation not valid for NIL"))
				| 	{exp=_, ty = Types.BOTTOM} => ()
				| 	_ => (ErrorMsg.error pos "invalid operation"));
					
					{exp = (), ty = Types.INT})
				end

		| trexp (A.RecordExp {fields,typ,pos}) = let  (* RecordExp *) 
			val actualType = actual_ty (lookup (tenv, typ, pos))						
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
		    		if eqTypes(t, #ty (trexp exp)) then () else ErrorMsg.error pos "Mismatching field types"
		    	end 	
		    val () = app checkFieldTypes fields

        	in
        		{exp = (), ty = actualType}
        	end

        | trexp (A.SeqExp l) = let											(* SeqExp *)
        	fun seqHelper [(exp,pos)] = trexp exp
              | seqHelper ((exp,pos)::tail) = (trexp exp; seqHelper tail)
              | seqHelper [] = trexp(A.NilExp)
        	in 
        		seqHelper l
        	end

        | trexp (A.AssignExp {var,exp,pos}) = let							(* AssignExp *)
        	val var_ty = #ty (trvar (var))
        	val exp_ty = #ty (trexp (exp))
        	in 
        		if (eqTypes(var_ty, exp_ty)) then {exp = (), ty = Types.UNIT}
        		else (ErrorMsg.error pos "type mismatch in var assignment";{exp = (), ty = Types.BOTTOM})
        	end

		| trexp (A.IfExp {test, then' = thenexp, else' = NONE, pos}) =  (* IfExp *)
        	(checkInt(trexp test, pos); checkUnit(trexp thenexp, pos);
        	{exp = (),ty = Types.UNIT})

        | trexp (A.IfExp {test, then' = thenexp, else' = SOME(elseexp), pos}) = let
        	val then_ty = #ty (trexp thenexp)
        	val else_ty = #ty (trexp elseexp)
        	in
        		(checkInt(trexp test,pos);
        		if eqTypes(then_ty, else_ty) then {exp = (), ty = then_ty}
        		else (ErrorMsg.error pos "then and else expressions must have same type"; 

        		{exp=(),ty=then_ty}))
        	end

		| trexp (A.WhileExp {test,body,pos}) = 							(* WhileExp *)
        		(checkInt (trexp test, pos);
        		 nestLevel := !nestLevel + 1;
        		 checkUnit (trexp body, pos);
        		 nestLevel := !nestLevel - 1;	
        		 
        		 {exp = (), ty = Types.UNIT})

        | trexp (A.ForExp {var, escape, lo, hi, body, pos}) = let			(* ForExp *)
        	val () = checkInt (trexp lo, pos)
        	val () = checkInt (trexp hi, pos)
        	val venv' = S.enter(venv, var, E.VarEntry{ty = Types.INT})  (* local variable*)
        	val () = (nestLevel := !nestLevel + 1)
        	val {exp, ty} = transExp (venv', tenv) body
        	val () = (nestLevel := !nestLevel - 1)
        	val () = checkUnit ({exp = exp, ty = ty}, pos)
        	in
        		{exp = (), ty = ty}
        	end

        | trexp (A.BreakExp(pos)) = 									(* BreakExp *)
        	if (!nestLevel <> 0) then {exp = (), ty = Types.UNIT}
        	else (ErrorMsg.error pos "Break must be within a loop"; {exp = (), ty = Types.BOTTOM})

		| trexp (A.LetExp{decs, body, pos}) = let							(* LetExp *)
        	val {venv = venv', tenv = tenv'} = transDecs(venv, tenv, decs)
        	in 
        		transExp(venv',tenv') body
        	end
        	
        | trexp (A.ArrayExp {typ, size, init, pos}) = let					(* ArrayExp *)
      		val {exp = _, ty = tyinit} = trexp init;
      		in
      			checkInt(trexp size, pos);
        		case S.look(tenv, typ) of 
             		NONE => (ErrorMsg.error pos "undeclared  type"; {exp = (), ty = Types.BOTTOM})
          		|   SOME t => case actual_ty t  of
          		 		Types.ARRAY (ty,unique) =>              
               			(if eqTypes(tyinit, ty) then {exp = (), ty = Types.ARRAY (ty,unique) }
               			else (ErrorMsg.error pos ("Expected: " ^ Types.toString ty ^ " Actual: " ^ Types.toString tyinit); {exp = (), ty = Types.BOTTOM}))
               	|   _ => (ErrorMsg.error pos (S.name typ ^" is not of array type"); {exp = (), ty = Types.BOTTOM})	
           	end
           	 	
		and trvar (A.SimpleVar(id,pos)) = (case Symbol.look(venv, id) of 
			SOME (E.VarEntry{ty}) => {exp = (), ty = actual_ty ty}
	  	  | _ => (ErrorMsg.error pos ("undefined variable " ^ Symbol.name id); {exp = (), ty = Types.BOTTOM}))

    	|   trvar (A.FieldVar(var, id, pos)) = (case trvar var of 
    			{exp, ty = Types.RECORD(fields,_)} => let 
                    fun idfinder (symid,_) = (symid = id)
                in
                    (case (List.find idfinder fields) of 
                    	SOME(_,ty) => {exp = (), ty = actual_ty ty}
                      | NONE       => (ErrorMsg.error pos ("record does not have this field" ^ Symbol.name id);
                                    {exp = (),ty = Types.BOTTOM}))
                end
      		|   {exp, ty} => (ErrorMsg.error pos "not a record type"; {exp=(), ty=Types.BOTTOM}))

    	|   trvar (A.SubscriptVar(var, exp, pos)) =
                (checkInt((trexp exp), pos);
                (case (#ty (trvar var)) of 
                	Types.ARRAY(ty, _) => {exp=(), ty=actual_ty ty}
                  | Types.BOTTOM => {exp = (), ty = Types.BOTTOM}
                  | _ => (ErrorMsg.error pos ("not an array type"); {exp=(), ty=Types.BOTTOM})))
	in 
		trexp 
	end

	and transTy (tenv, A.NameTy(s,pos)) = lookup(tenv,s,pos)
	|   transTy(tenv, A.RecordTy l) = let 
		fun convFieldToTuple {name,escape,typ,pos} = (name,lookup(tenv,typ,pos))
		val tupleList = map convFieldToTuple l
		in
			Types.RECORD(tupleList,ref ())
		end
	|   transTy (tenv, A.ArrayTy(s,pos)) = Types.ARRAY(lookup(tenv,s,pos),ref ())

	and transDecs (venv, tenv, l) = let
		val res = foldr transDecName {venv=venv, tenv=tenv} l
	in
		foldl transDec res l
	end

	and transDecName (A.VarDec l, {venv,tenv}) = {venv = venv, tenv = tenv}
	|   transDecName (A.TypeDec l, {venv,tenv}) = let
		fun addHeaders (name,tenv) = (S.enter (tenv, name, Types.NAME(name, ref NONE)))
		val tenv' = foldl addHeaders tenv (map #name l)
	in
		{venv = venv, tenv = tenv'}
	end
	|   transDecName (A.FunctionDec l, {venv,tenv}) = let
		fun addHeader (name,venv) = (print ("addfunction: " ^ (Symbol.name name));
			(S.enter (venv, name, E.NameEntry(name, ref NONE))))
		fun getResultType (SOME(rt,pos)) = (case S.look(tenv,rt) of 
											SOME(t)=> t
										  | NONE => (ErrorMsg.error pos "Return type not valid";Types.BOTTOM))
		|   getResultType NONE = Types.UNIT
					
		fun transparam{name,escape,typ,pos} = case S.look(tenv,typ) of 
											  SOME t => {name=name,ty=t}
								            | NONE => (print ((S.name typ)^" undefined type"); {name=name,ty=Types.UNIT})
		fun addHeaders ({name,params,result,body,pos}, venv) = let 
			val result_ty = getResultType result
			val params' = map transparam params
			in 
				(print ("addfunction: " ^ (Symbol.name name));
				(map (fn s => print ((S.name name) ^ "e:" ^ (Types.toString s) ^ "\n")) (map #ty params'));
				S.enter(venv,name,E.NameEntry(name, ref (SOME (E.FunEntry{formals=map #ty params',result=result_ty})))))
			end

		val venv' = foldl addHeaders venv l
	in
		{venv = venv', tenv = tenv}
	end

	and transDec (A.VarDec{name,escape,typ=NONE,init,pos},{venv,tenv}) = let 
		val {exp,ty} = transExp(venv,tenv) init
		in 
			{tenv=tenv, venv = S.enter(venv,name,E.VarEntry{ty = ty})}
		end

	|	transDec (A.VarDec{name, escape, typ = SOME (symbol, pos), init, pos = varpos}, {venv, tenv}) = let 
		val {exp,ty} = transExp(venv,tenv) init
		val ty2 = actual_ty (lookup (tenv,symbol,pos))		
		in 
			(print(Types.toString(ty) ^ ":" ^ Types.toString(ty2));
			if ty = ty2 then {tenv=tenv, venv = S.enter(venv,name,E.VarEntry{ty = ty})}
			else (ErrorMsg.error pos "Mismatching types"; {tenv=tenv, venv = S.enter(venv,name,E.VarEntry{ty = ty})}))
		end

	|	transDec (A.TypeDec l,{venv,tenv}) = let
		fun replace(Types.NAME(n,r), ty) = r := SOME ty
		  | replace(_,_) = raise Fail("not TypeDec") 
		fun replaceHeaders {name,ty,pos} = replace(Option.valOf(S.look (tenv, name)), transTy(tenv, ty))
		val () = app replaceHeaders l
		(*val c = (map (fn s => print ((Symbol.name s) ^ ":" ^ Types.toString
			(actual_ty (Option.valOf(S.look(tenv', s)))) ^ "\n")) names)*)
		in
			{venv = venv, tenv = tenv}
	    end

(*	| 	transDec (A.FunctionDec[{name,params,result=SOME(rt,pos'),body,pos}],{venv,tenv}) = let 
		val result_ty = lookup(tenv,rt, pos')
		fun transparam{name,escape,typ,pos} = {name=name,ty=lookup(tenv, typ, pos)}
		val params' = map transparam params
		val () = case S.look(venv, name) of
			      SOME (E.NameEntry(s, r)) => r := SOME (E.FunEntry{formals=map #ty params',result=result_ty})
			    | _ => raise Error
		fun enterparam ({name,ty},venv) = S.enter(venv,name,E.VarEntry{ty=ty})
		val venv'' = foldl enterparam venv params' 
		in 
			transExp(venv'',tenv) body; {venv=venv,tenv=tenv}
		end*)

	| 	transDec (A.FunctionDec l,{venv,tenv}) = let 
		fun getResultType (SOME(rt,pos)) = (case S.look(tenv,rt) of 
											SOME(t)=> t
										  | NONE => (ErrorMsg.error pos "Return type not valid";Types.BOTTOM))
		|   getResultType NONE = Types.UNIT
					
		fun transparam{name,escape,typ,pos} = case S.look(tenv,typ) of 
											  SOME t => {name=name,ty=t}
								            | NONE => (print ((S.name typ)^" undefined type"); {name=name,ty=Types.UNIT})
		fun processBodies {name,params,result,body,pos} = (let

			val result_ty = getResultType result
			val params' = map transparam params
			fun enterparam ({name, ty}, venv) = S.enter(venv,name,E.VarEntry{ty=ty})
			val venv' = foldl enterparam venv params' 
			val bodyType = #ty (transExp(venv',tenv) body)
			in
				if eqTypes(bodyType,result_ty) then () else (ErrorMsg.error pos "function does not evaluate to correct type")
			end)

			val () = app processBodies l
		in 
			{venv=venv,tenv=tenv}
		end

  	fun transProg ast = let 
		val {exp = result, ty = _ } = transExp (E.base_venv, E.base_tenv) ast
	in 
		result
	end
end