#set page(margin: 1cm)
#set page(numbering: "i")
#set text(lang: "pl")
#set heading(numbering: "1.")
//#set text(font: "New Computer Modern")
#set grid(column-gutter: 16pt)
#show link: underline
#grid(
  columns: (1fr, 1fr),
  align: horizon,
  [
    #set par(justify: true)
    Te notatki są moją próbą skondensowania całego wykładu dr. Przybyło w kilka stron gęstej "ściągi".
    Nie zastepują one wykładu, a uzupełniają go.

    Algebra był moim ulubionym przedmiotem w pierwszym semestrze, więc do dzisiaj zależy mi na jakości tych notatek.
    Jeśli znajdziesz jakiś błąd lub masz inne uwagi -- pisz!

    Ostatnio zmodyfikowane: 2024-04-16. \
    #link("https://dzwdz.net/agh-notes")
  ],
  outline()
)

#let Dp = rotate(180deg, $D$)

= Liczby zespolone
$z_1 dot z_2 = (x_1 x_2 - y_1 y_2, space x_1 y_2 + x_2 y_1)$ #h(1fr)
$z^(-1) = ((x+y)/(x^2 + y^2), (x-y)/(x^2+y^2))$ #h(1fr)
$overline(x + y i) = x - y i$ #h(1fr)
$arg z in [0; 2pi)$ \
*Wzór de Moivre'a*: $z^n = |z|^n (cos(n phi) + i sin (n phi)) = |z|^n e^(i n phi)$ #h(1fr)
$root(n, z) = root(n, |z|)(cos(phi + 2k pi)/n + i sin(phi + 2k pi)/n)$ \
$z overline(z) = |z|^2$

*Tw. Bézout*: $W(z_0) = 0 <==> exists P in CC[x] : W(z)=(z-z_0)P(z)$ \
*Tw. o pierw. wymiernych*:
$RR[x] in.rev a_n x^n + ... + a_0 = W(x), wide
W(p/q) = 0 and p,q "coprime" ==> (a_0|p) and (a_n|q)$
*Zasadnicze tw. algebry*: $forall W in CC[x] : exists z : W(c) = 0$ \
*Tw. o pierw. zespolonych wielomianu rzecz.*: $W in RR[x], space W(z) = 0 <==> W(overline(z)) = 0$

= Relacje
$R = (X, "gr"R, Y)$ \
*naddziedzina* $= X supset D_f$ \
*zapas* $= Y supset Dp_R$

1. $R$ *zwrotne* $<==> forall x in X: x R x$
2. $R$ *symetryczne* $<==> forall x,y in X: x R y <=> y R x$
3. $R$ *przechodnie* $<==> forall x,y,z in X : (x R y and y R z => x R z)$
4. $R$ *antysymetryczne* $<==> forall x, y in X: (x R y and y R x => x = y)$
5. $R$ *asymetryczne* $<==> forall x, y in X : (x R y => not space y R x)$
6. $R$ *spójne* $<==> forall x, y in X : (x R y or y R x or x = y)$

$R$ *relacją równoważności* $<==> R$ zwrotne(1), symetryczne(2), przechodnie(3) \
*klasa równoważności*: $[x] := {y : x R y}$ \
*zbiór ilorazowy*: $X \/_R := {[x] : x in X}$

$R$ (słabym) *porządkiem* (częściowym) $<==> R$ zwrotne(1), antysymetryczne(4), przechodnie(3) \
$R$ *porządkiem totalnym* / *liniowym* $<==> R$ porządkiem i spójne(6) \
$overline(M)$ (jedynym) *el. największym* $<==> forall x : x lt.curly.eq overline(M)$ #h(1fr) (*el. najmniejszy* analogicznie)\
$M_max$ *el. maksymalnym* $<==> forall x : (M_max lt.curly.eq X => M_max = X)$ #h(1fr) (*el. minimalny* analogicznie)\
$M in X$ *majorantą* $A subset X$ $<==> forall x in A : x lt.eq.curly M$ #h(1fr) (*minoranta* analogicznie) \
*kres górny* $A$ w $X =$ element najmniejszy zbioru majorant $= sup A$ \
*kres dolny* $A$ w $X =$ element największy zbioru minorant $= inf A$

$C$ *łańcuchem* $<==> C in X and (C, R|_(C times C)) "liniowo uporządkowane"$

#pagebreak()

= Struktury
Dla $(X, circle)$:
0. $circle$ *wewnętrzne* $<==> forall x, y in X : x circle y in X$
1. $circle$ *łączne* $<==> forall x, y, z : (x circle y) circle z = x circle (y circle z)$
2. $circle$ *przemienne* $<==> forall x, y : x circle y = y circle x$
3. $e in X$ *el. neutralnym* $<==> forall x : e circle x = x = x circle e$
4. $x'$ *el. odwrotnym* $x$ $<==> x' circle x = e = x circle x'$
5. $*$ *rozdzielne* względem $plus.circle$ $<==> forall x,y,z : (x plus.circle y) * z = x * z plus.circle y * z$ i w drugą stronę

$(X, plus.circle)$ *grupą* $<==>$ $plus.circle$ wewnętrzne(0), łączne(1), $exists e$ (3), $forall x exists x'$ (4) \
$(X, plus.circle)$ *grupą abelową* $<==>$ $(X, plus.circle)$ grupą $and$ $plus.circle$ przemienne(2) \
W szczególności skoro $exists e$, $x != emptyset$.

$(X, plus.circle, *)$ *pierścieniem* $<==>$ $(X, plus.circle)$ grupą abelową $and (X, *)$ wewnętrzne(0), łączne(1), rozdzielne względem $plus.circle$ \
$(X, plus.circle, *)$ *pierścieniem przemiennym*  $<==> (X, *)$ przemienne \
*działanie addytywne*: $plus.circle$, el. neutralny to $bold(0)$ \
*działanie multiplykatywne*: $*$, el. neutralny, _jeśli istnieje_, to $bold(1)$.
Wtedy mamy *pierścień z jedynką*. \
$x, y$ *dzielnikami 0* $<==> x, y != bold(0) and x * y = bold(0)$ \
*pierścień całkowity*: z jedynką, bez dzielników zera \
$(K, plus.circle, *)$ *ciałem* $<==>$ pierścieniem całkowitym z el. odwrotnymi względem mnożenia \
$(K, plus.circle, *)$ *ciałem* $<==>$ $(K, plus.circle)$ grupą abelową $and$ $(K\\{0}, *)$ grupą $and$ $*$ rozdzielne względem $plus.circle$ \

$f$ *homo/*hyhy*/morfizmem grup*
$<==> forall a, b : f(a) + f(b) = f(a plus.circle b)$
#h(1fr) (nie musi być różnowartościowy!)\
$f$ *homomorfizmem pierścieni*
$<==> forall a, b : f(a) + f(b) = f(a plus.circle b) and f(a) * f(b) = f(a dot.circle b)$

$(V, K, +, *)$ *przestrzenią wektorową*:
- $(K, plus.circle, dot.circle)$ ciałem przemiennym, $(V, +)$ grupą abelową ($V != emptyset$)
- $forall u, v in V, alpha in K : a * (u + v) = a * u + a * v$
- $forall v in V, a, b in K : (a dot.circle b) * v = a * (b dot.circle v)
and (a plus.circle b) * v = a * v + b * v$
- $forall v in V: bold(1) * v = v$

$U subset V, space U != emptyset$ *podprzestrzenią* $<==> forall u, v in U, k in K: u+v in U and k * v in U$ \
Równoważna charakterystyka: $forall a, b in K, space u, v in U : a * u + b * v in U$ \
Uogólniona równoważna: $forall a_1, ..., a_n in K, v_1, ..., v_n in U : a_1 * v_1 + ... + a_n * v_n in U$ \
$dim U <= dim V, wide dim U = dim V => U=V$ \
$dim(U_1 + U_2) = dim U_1 + dim U_2 - dim U_1 sect dim U_2$ \
$U_1 + U_2 = U_1 plus.circle U_2 <==> U_1 sect U_2 = {overline(0)}$ \

$B$ *bazą* $V$ $<==>$ $B$ maks. zbiorem liniowo niezależnych wektorów $<==>$ $B$ min. zbiorem wektorów rozpinających $V$ \
*reper bazowy* $B = (e_1, e_2, ...)$: baza z ustalona kolejnością \
*współrzędne* wzgledem $B$: $[k_1, k_2, ...]_B = e_1k_1 + e_2k_2 + ...$

#pagebreak()
= Macierze
$A = [a_(i j)]_(m times n) =
mat(delim:"[",
  a_11, a_12, ..., a_(1n);
  a_21, a_22, ..., a_(2n);
  dots.v, dots.v, dots.down, dots.v;
  a_(m 1), a_(m 2), ..., a_(m n);
)_(m times n)$

$[a_(i j)]_(m times n) [b_(i j)]_(n times o) = [c_(i j)]_(m times o) wide
"gdzie" c_(i j) = sum_(k=1)^n a_(i k) b_(k j)$

$det A = sum_(sigma in S_n) epsilon(sigma) dot a_(1 sigma(1)) dot a_(2 sigma(2)) dot ... dot a_(n sigma(n)) wide$ gdzie $epsilon(sigma) =$ znak permutacji $sigma$ \
$det A = 0 <==$ wiersze/kolumny nie są liniowo niezależne \
pomnożenie jednego z wierszy przez $n$ mnoży wyznacznik przez $n$  $ wide => det n A = n^2 det A$ \
przestawienie wierszy/kolumn zmienia znak \
*Tw. Cauchy'ego*: $det(A B) = det A dot det B$

*Minor* stopnia $k$: wyznacznik dowolnej podmacierzy $k times k$ \
*Minor odpowiadający* $a_(i j)$ (w macierzy $A_(k times k)$) $= M_(i j) =$ wyznacznik po pozbyciu się wiersza/kolumny $a_(i j)$ \
*Dopełnienie algebraiczne* $a_(i j)$ $= A_(i j) = (-1)^(i+j) dot M_(i j)$ \
*Twierdzenie Laplace'a*: $forall j in [1,n] : det A = sum_(i=1)^n a_(i j) A_(i j)$

*Rząd macierzy* $= r(A) =$ maks. liczba liniowo niezależnych wierszy/kolumn $=$ maks. stopień minora niezerowego

*operacje elementarne*: zamiana, dodanie kombinacji liniowej, pomnożenie [wierszy/kolumn]

*macierz odwrotna*:
$A A^(-1) = A^(-1) A = I$,
$wide exists A^(-1) <==> det A != 0 <==> A$ *nieosobliwa* $<==> r(A_(n times n)) = n$ \
$det (A^(-1)) = (det A)^(-1), wide (A^T)^(-1) = (A^(-1))^T, wide (A B)^(-1) = B^(-1) A^(-1)$ \
$A^(-1) = (det A)^(-1) (A^D)^T, wide$ gdzie $A^D = [A_(i j)] =$ *macierz dopełnień algebraicznych*

= Układy równań
$A_(m times n) = $ macierz współczynników/główna #h(1fr)
$B_(m times 1) =$ macierz wyrazów wolnych #h(1fr)
$[A|B] =$ macierz uzupełniona \
$A dot X_(m times 1) = B$ \
*układ jednorodny* $<==> B = overline(0)$ \
*układ oznaczony* $<==>$ dokładnie jedno rozwiązanie \
*układ nieoznaczony* $<==>$ więcej rozwiązań \
*układ sprzeczny* $<==>$ bez rozwiązań \

*układ kwadratowy* $<==> m=n <==> A$ kwadratowe \
$wide$*układ Cramera* $<==> m=n and det A != 0 ==>$
  dokładnie jedno rozwiązanie, $x_j = (det A)^(-1) dot D_x_j$ \
$wide det A = 0 and exists j : D_x_j != 0 <==>$ sprzeczny \
$wide det A = 0 and forall j : D_x_j = 0 <==>$ nieoznaczony $or$ sprzeczny \

*Tw. Kroneckera-Capellego*: układ ma rozwiązanie $<==> r(A) = r([A|B])$ \
$wide r(A) = r([A|B]) = n <==>$ układ oznaczony

#pagebreak()

= Geometria analityczna
$P = (x,y,z), space arrow(v) = [x,y,z]$

*iloczyn skalarny* (dot product): $u dot v := sum u_i v_i = ||u|| dot ||v|| cos angle.spheric(u, v) in RR$ \
$||v|| = sqrt(v dot v), wide forall u, v : |u dot v| <= ||u||dot||v||$

*kąt między wektorami*:
$angle.spheric(u, v) in [0; pi/*)*/], space cos angle.spheric(u, v) = (u dot v)/(||u|| dot ||v||)$ \
*prostopadłe*: $angle.spheric(u,v) = pi/2 <=> u perp v <=> u dot v = 0$ \
*równoległe*: $angle.spheric(u,v) = 0 <=> u || v <=> u, v "liniowo niezależne"$

// na prawo od definicji iloczynu
#place(right,
$ u times v = mat(delim: "|",
  arrow(i), arrow(j), arrow(k);
  thin u_1, thin u_2, thin u_3;
  v_1, v_2, v_3
) $
)

*iloczyn wektorowy*: $times : (arrow(E_3))^2 in.rev (u,v) -> u times v in arrow(E_3)$ \
$||u times v|| = ||u||dot||v|| sin angle.spheric(u, v) wide (therefore u || v => u times v = overline(0))$ \
$||u times v|| =$ *pole równoległoboku* rozpiętego przez $u, v$

// na prawo od definicji iloczynu
#place(right,
$ (u times v) dot w = mat(delim: "|",
  u_1, u_2, u_3;
  v_1, v_2, v_3;
  w_1, w_2, w_3;
) $
)

*iloczyn mieszany*: $(u times v) dot w, wide u,v,w in arrow(E_3)$ \
*objętość równoległościanu* rozpiętego przez $u,v$ $= (u times v) dot w$ \
.

*płaszczyzna* $pi$, $space P_0 = (x_0, y_0, z_0) in pi, space n = [A, B, C] perp pi, space n != overline(0)$ \
równanie *normalne*: $0 = arrow(P_0 P) dot n = A(x - x_0) + B(x - x_0) + C(z - z_0)$ \
równanie *ogólne*: $A x + B y + C z + D = 0, wide D = -A x_0 - B y_0 - Z z_0$ \
równanie *parametryczne*: $(x,y,z)=P_0 + t u + s v wide t,s in RR wide u, v || pi, space not(u || v)$ \
równanie *odcinkowe*: $x/a + y/b + z/c = 1$ *TODO* co? \

// odległość punktu $Q = (x, y, z)$: $abs(A x + B x + C x + D)/sqrt(A^2 + B^2 + C^2)$ #h(1fr) liczymy "błąd" równania ogólnego \

// odległość płaszczyzn $pi_1 || pi_2$: $d(pi_1, pi_2) = d(pi, P_2) = abs(A x_2 + B y_2 + C z_2 + D_1) / sqrt(A^2 + B^2 + C^2) = abs(D_1 - D_2) / sqrt(...)$

*prosta* $l$, $space P_0 = (x_0, y_0, z_0) in l, space v = [a,b,c] || l, space v != overline(0)$ \
równanie *parametryczne*: $P=P_0+ t v wide t in RR$ \
równanie *kierunkowe*: $(x-x_0)/a = (y-y_0)/b = (z-z_0)/c$ \
równanie *krawędziowe*: dwa równania ogólne $pi_1, pi_2$, gdzie $l in pi_1, pi_2 and not (pi_1 || pi_2)$

// odległość punktu $Q$: $(||arrow(P_0P) times v||)/(||v||)$

// odległość prostych $l_1, l_2$: $abs((v_1 times v_2) dot arrow(P_1 P_2))/(|| v_1 times v_2 ||)$

*Nierówność Cauchy'ego, Buniakowskiego, Schwarza*:
$|u dot v| <= ||u|| dot ||v||, wide |u dot v| = ||u|| dot ||v|| <==> u || v$

== Odległości
$
d(pi, (x,y,z)) &= abs(A x + B x + C x + D)/sqrt(A^2 + B^2 + C^2) wide "(liczymy \"błąd\" równania ogólnego)"\

pi_1 || pi_2 => space d(pi_1, pi_2) = d(pi, P_2) &= abs(A x_2 + B y_2 + C z_2 + D_1) / sqrt(A^2 + B^2 + C^2) = abs(D_1 - D_2) / sqrt(...) \

d(P, l) &= (||arrow(P_0P) times v||)/(||v||) \

d(l_1, l_2) &= abs((v_1 times v_2) dot arrow(P_1 P_2))/(|| v_1 times v_2 ||) \
$




#pagebreak()
= Odwzorowania liniowe
Niech $V, W$ będą przestrzeniami wektorowymi nad ciałem $K$. \
$f : V -> W$ *odzworowaniem liniowym* $<==> forall u,v : f(u+v)=f(u)+f(v) and forall v, alpha : f(alpha v) = alpha f(v)$


*jądro* $f = "Ker"f := {v in V : f(v) = 0} wide wide thin thin = f^(-1){overline(0)_W}$ \
*obraz* $f = "Im"f := {w in W: exists v :f(v) = w} wide = f(V)$ \
$dim V = dim "Ker"f + dim "Im"f$ \
*rząd odwzorowania* $= r(f) = dim "Im"f$

$f$ *monomorfizmem* $<==>$ różnowartościowe $<==>$ injektywne \
$f$ *epimorfizmem*  $<==>$ surjektywne $<==> "Im"f = W$ \
$f$ *izomorfizmem*  $<==>$ bijektywne \
$f$ *endomorfizmem* $<==> V = W$ \
$f$ *automorfizmem* $<==>$ endomorfizmem bijektywnym \
$f$ *formą liniową* $<==>$ W = K #h(1fr) np. $f:RR^3->RR, f(x,y,z)=2x+y$

$V, W$ *izomorficzne* $<==> V thin ~ thin W <==> exists$ izomorfizm $V -> W$ \
$f: V->W$ izomorfizmem $<==> f^(-1) : W->V$ izomorfizmem \
$V thin~thin W <==> space (dim V = dim W < infinity) space and space$ $(V,W$ są nad tym samym ciałem$)$

$f$ endomorfizmem $and M_f (B_1, B_2)$ nieosobliwe $<==>$ $f$ automorfizmem (izomorfizmem)

$P_(B -> B') = M_id_V (B', B)$

*Tw. o zmianie macierzy odwzorowania przy zmianie baz*: \
$wide M_f (B'_V, B'_W) = P_(B'_W -> B_W) dot M_f (B_V, B_W) dot P_(B_V -> B'_V)$

#linebreak()

Niech $A = M_f (B)$, w dowolnej bazie $B$, a $f$ będzie endomorfizmem. \
$lambda in K$ *wartością własną* $f$
$<==>$ $exists v in V \\ {overline(0)}: f(v) = lambda v$
$<==>$ $det(A - lambda I) = 0$ \
*wielomian charakterystyczny* $f$: $Delta(lambda) := det(A - lambda I) = (-lambda)^n + ... + det A$ \
$v = [a_1, ...]_B != overline(0)$ *wektorem własnym* odpowiadającym $lambda$
$<==>$ $f(v) = lambda v$
$<==>$ $(A - lambda I) mat(delim:"[",a_1;...;a_n) = overline(0)$ \
$V_lambda = {v in V : f(v) = lambda v}$ jest podprzestrzenią wektorową.

#pagebreak()
#set heading(bookmarked: false, outlined: false)
= Etc.

*injekcja*: funkcja różnowartościowa

*surjekcja*: funkcja "na" zbiór Y - przyjmuje wszystkie wartości ze zbioru Y

*izomorfizm*: homomorfizm bijektywny \
$h "monomorfizmem z" A "na" B "i bijekcją" => h "izomorfizmem"$

*automorfizm*: izomorfizm na siebie

*monomorfizm*: homomorfizm iniektywny

=== TODO
bardziej konsekwentne oznaczanie wektorów, potencjalnie funkcja jak na fiz
