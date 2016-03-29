type EitherNB = Left bool
              | Right num

case Left(true) of
| Left(b) => b
| Right(b) => b
