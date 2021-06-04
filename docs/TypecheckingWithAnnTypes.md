
* Notes: Typechecking with anntypes

When typechecking the following:

```julia
function f(g)
   g(1) + g(2)
end
function h(x) :: X -> (A -> R)
  a -> 2x + 3a
end
```
Wobei h eigentlich den typen hat (eckige klammern sind Fun[]'s)
```
h :: [(X@2*s_A -> [(A@3 -> R) @ s_A]) @ s_X]
```
und das checken von h so abläuft dass wir erstmal den inneren term typechecken, also ```{x @ 2, a @ 3} |- 2x + 3a```, dann für das innere lambda, den {a @ 3}-teil rausholen, und in den arrow type schreiben, und den ganzen kontext mit dem neuen faktor s_A multiplizieren, dass heißt wir haben:
```
{x @ (2 * s_A)} |- a -> 2x + 3a : [(A@3 -> R) @ s_A]
```
Wenn wir jetzt das "lambda" außen drum checken ist das gute, dass der s_A factor ja mit einfließt in die sensitivity, wir kriegen, wenn wir jetzt x aus dem kontext holen ja:
```
{} |- x -> a -> 2x + 3 a : [(X@2*s_A -> [(A@3 -> R) @ s_A]) @ s_X]
```
Wobei der leere kontext mit s_X multipliziert wurde, aber das ist jetzt egal.
Das heißt, wenn wir dann etwas in h rein tun, zb.
```
{q @ s_Q} |- arg q :: Q
```
Wobei s_Q hier der preskalierungsfaktor ist, dann wird ja s_Q := (2 * s_A) gesetzt, wir kriegen also
```
{q @ 2 * s_A} |- h q :: [(A@3 -> R) @ s_A]
```
was perfekt ist, weil wenn wir jetzt f(h q) aufrufen, dann wird ja die funktion (h q) in f 2 mal verwendet, also wollen wir den gesamten kontext von (h q) auch mit 2 multiplizieren. Und glücklicherweise ist das auch genau das was automatisch passiert, wenn wir wie normal (s_A := 2) setzen, und wir kriegen sowas wie
```
{q @ 2 * 2} |- f (h q) :: ...
```

