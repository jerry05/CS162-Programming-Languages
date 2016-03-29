type OptionN = Some num
            | None
            

let mapO = (rec mapInner : ((num) => num, OptionN) => OptionN = 
            (f: (num) => num, o: OptionN) => case o of
                | None => None
                | Some(n)  => Some(f(n)) in mapInner)
    in mapO(((x: num) => x + 1), Some(1))
