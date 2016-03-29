type ListN = ListN [ head: num, tail: ListN ]
           | Nil

let cons = ((h: num, t: ListN) => 1),
    empty = Nil,
    mapM = (rec mapInner: ((num) => num, ListN) => ListN = 
                (f: (num) => num, xs: ListN) => 
                    case xs of
                      | Nil => Nil
                      | ListN(r) => ListN( [head = f(r.head), tail = mapInner(f, r.tail)] )
                in mapInner)
  in mapM((n: num) => n + 10, ListN( [head = 1, tail = Nil] ))
