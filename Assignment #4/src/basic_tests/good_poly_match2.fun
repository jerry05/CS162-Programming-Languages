type Foo ['A] = Bar 'A | Baz 'A

case Bar<num>(3) of
| Bar(b) => b
| Baz(b) => b
