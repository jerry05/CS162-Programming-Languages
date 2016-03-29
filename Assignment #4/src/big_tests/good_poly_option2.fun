type Option['A] = Some 'A | None

let polyMap = ['A, 'B](f: ('A) => 'B, o: Option<'A>) =>
     case o of
     | None => None<'B>
     | Some(a) => Some<'B>(f(a))
in polyMap<num, num>((n: num) => n + 1, Some<num>(2))

