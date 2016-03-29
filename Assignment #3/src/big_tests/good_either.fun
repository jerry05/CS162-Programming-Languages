type EitherNB = Left bool
              | Right num

let eitherL = Left(true),
    eitherR = Right(1),
    eitherM = (rec mapInner: ((num) => num, EitherNB) => EitherNB =
                (f: (num) => num, xs: EitherNB) =>
                    case xs of
                      | Left(b) => Left(b)
                      | Right(n) => Right(f(n))
                in mapInner)
  in eitherM((n: num) => n + 1, eitherL)


