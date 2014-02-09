val listint = List.tabulate(49, fn x => x+1)
List.map (fn filenumber => (Parse.parse ("test/test" ^ Int.toString(filenumber) ^ ".tig"))) listint