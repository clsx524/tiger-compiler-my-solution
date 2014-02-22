structure Compiler
=
struct 
  	fun compile filename = Semant.transProg(Parse.parse filename)
end