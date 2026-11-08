# Cierre de H1 y del teorema de tres cuadrados en casquetes

Esta nota desarrolla el ensamblaje matemático. La confirmación de compilación y axiomas corresponde al informe de auditoría del mismo árbol; la existencia de esta nota no sustituye esa comprobación.

## 1. Enunciados y cuantificadores

H1, denominado `DukeSquarefree`, afirma lo siguiente. Dados un vector unitario `u∈ℝ³` y un número `ε>0`, existe `T₀` tal que todo entero libre de cuadrados `t≥T₀`, con `t≡3 (mod 8)`, tiene una representación entera `x` que cumple

\[
|x|^2=t,\qquad |x_i-\sqrt t\,u_i|\le\varepsilon\sqrt t\quad(i=0,1,2).
\]

El resultado final, `ThreeSquaresDense`, tiene los mismos cuantificadores y conclusión, pero admite todos los enteros suficientemente grandes congruentes con tres módulo ocho. La reducción entre ambos enunciados utiliza H2, el resultado ya desarrollado sobre cuatro cuadrados en casquetes.

No se cambia el tamaño del casquete con el entero representado. El umbral se escoge después de fijar la dirección y el casquete, y sirve para todos los enteros posteriores permitidos.

## 2. Por qué basta un ahorro que dependa del grado

Escribamos `r₃(t)` para el número de representaciones enteras ordenadas, con sus signos, y

\[
W_P(t)=\sum_{|x|^2=t}P(x).
\]

El argumento del casquete utiliza el polinomio

\[
k_{u,K}(x)=\left(\frac{1+u\cdot x/\sqrt t}{2}\right)^K.
\]

Sobre la esfera su media es `1/(K+1)`. Fuera de un casquete algo menor que el deseado, se tiene `0≤k_{u,K}(x)≤ρ^K`, para un `ρ<1` que sólo depende de la anchura del casquete. Escogemos primero `K` para que `(K+1)ρ^K<1/2`.

La expansión de este polinomio y su descomposición de Fischer sólo emplean grados entre cero y `K`. Por eso basta disponer, para cada grado positivo `d`, de algún `η_d>0` con

\[
|W_P(t)|\le C_P t^{d/2+1/2-\eta_d}
\]

cuando `P` es armónico homogéneo de grado `d`. Tomamos el mínimo de los ahorros para los grados `1,…,K`; incluir el valor auxiliar positivo del grado cero no cambia la positividad. Ese mínimo `η_K` es positivo. No se supone un ahorro uniforme sobre todos los grados.

Las sumas de grado impar se anulan: los puntos `x` y `−x` tienen contribuciones opuestas. Para los grados pares al menos dos, `weyl_iso_even` proporciona el ahorro para potencias de formas lineales isotrópicas complejas. El argumento de Vandermonde y el cálculo de la dimensión del espacio armónico permiten escribir cualquier armónico homogéneo como combinación de esas potencias. La suma de los valores absolutos de sus coeficientes queda absorbida en `C_P`.

La inducción de Fischer mantiene el grado acotado por `K`. Se obtiene

\[
\left|\sum_{|x|^2=t}k_{u,K}(x)-\frac{r_3(t)}{K+1}\right|
\le C_{u,K}t^{1/2-\eta_K}.
\]

Los módulos `DegreewiseWeyl.lean` e `IsoDegreewiseWeyl.lean` explicitan este orden de elección: primero el casquete, luego `K`, después el mínimo positivo `η_K`. El resultado de grados pares procede de `WeylFinal.lean`; no se confunde con la constante clásica óptima de Iwaniec.

## 3. El valor L en la frontera de convergencia

Para `n≡3 (mod 8)`, sea `χ_n` el carácter de Jacobi módulo `n`. Es real, no principal y satisface `χ_n²=1`. Sus sumas parciales están acotadas. La sumación parcial da

\[
\sum_{1\le k\le M}\frac{\chi_n(k)}k
\longrightarrow L(1,\chi_n).
\]

No se usa convergencia absoluta en `s=1`. El módulo `B3_SchiLimit.lean` adapta el argumento de sumación parcial de Mathlib para obtener este límite a partir de las sumas parciales acotadas. El valor del límite se identifica mediante la representación integral de la continuación analítica.

La representación integral y el teorema de Siegel se importan de las pruebas registradas de `goldbach-lean`, commit `6d7ae7b40fb5550e836456fd2ff4d8587157aee7`. `B3_VerifiedInputs.lean` suministra ambos contratos mediante esas pruebas; no los declara como axiomas ni los deja como parámetros del teorema final.

## 4. De las clases de residuos a una cota inferior de r₃

Supongamos además que `n` es libre de cuadrados. Sea `τ(n)` su número de divisores y consideremos el conjunto

\[
G_n=\{-z^2/2\pmod n:z\text{ es una unidad módulo }n\}.
\]

El dos es invertible porque `n` es impar. Todas estas clases son unidades y en ellas `χ_n` vale uno. Una clase tiene a lo sumo `τ(n)` preimágenes: al dividir dos preimágenes por una de ellas se obtiene una solución de `u²=1 mod n`, y, para `n` libre de cuadrados, esas soluciones se inyectan en los divisores de `n`. Por tanto

\[
\varphi(n)\le\tau(n)|G_n|.
\]

Definimos `χ₁(m)=Σ_{d|m}χ_n(d)` y

\[
S_n(M)=\sum_{\substack{1\le m\le M\\m\bmod n\in G_n}}\chi_1(m).
\]

El método de la hipérbola y la ortogonalidad de caracteres, desarrollados en `B3_Hyperbola.lean` y `B3_Asymp.lean`, dan para cada `c∈G_n`

\[
\frac1M\sum_{\substack{1\le m\le M\\m\equiv c\ (n)}}\chi_1(m)
\longrightarrow\frac{2L(1,\chi_n)}n.
\]

Se suman estos límites sobre el conjunto finito `G_n`. Para cada entero contado, la condición de su clase proporciona `n | 2t²m+1` para algún entero `t`. Los lemas aritméticos existentes inyectan los objetos contados por `χ₁(m)` en representaciones de `m` por las formas binarias reducidas que pertenecen a `GoodSet n`. No se necesita la fórmula exacta de Gauss para el número de clases.

Para una forma `f(x,y)=ax²+bxy+cy²` de discriminante `−n`, el módulo `B3_Ellipse.lean` demuestra

\[
\#\{(x,y):1\le f(x,y)\le M\}
\le\frac{8M}{\sqrt n}+6\sqrt a\sqrt M+1.
\]

Se suma sobre `GoodSet n`, se divide por `M` y se deja tender `M` a infinito. El conjunto de formas es finito para este `n`, de modo que los términos de orden `√M` y los constantes desaparecen. Resulta

\[
\frac{2|G_n|L(1,\chi_n)}n
\le\frac{8|\mathrm{GoodSet}(n)|}{\sqrt n}.
\]

La construcción de formas a partir de representaciones ternarias tiene fibras de tamaño a lo sumo dieciocho. Así,

\[
|\mathrm{GoodSet}(n)|\le18r_3(n),\qquad
\varphi(n)L(1,\chi_n)\sqrt n\le72n\tau(n)r_3(n).
\]

El valor `L(1,χ_n)` es real por el límite de sumas reales. Es no negativo porque `S_n(M)` es no negativo y `G_n` no es vacío. Esto permite multiplicar las desigualdades anteriores sin cambiar su dirección.

Por último, la identidad `n=Σ_{d|n}φ(d)` y la divisibilidad `φ(d)|φ(n)` para `d|n` implican `n≤τ(n)φ(n)`. Multiplicamos la última cota por `τ(n)` y cancelamos `n>0` para obtener

\[
\boxed{\sqrt n\,L(1,\chi_n)\le72\tau(n)^2r_3(n).}
\]

Este argumento compara cantidades finitas y sus límites. No presupone una fórmula de número de clases ni una equidistribución de representaciones.

## 5. El ahorro inferior que necesita el casquete

Fijado `ε>0`, ponemos `δ=min(ε,1)`. Siegel da un `c_s>0`, uniforme en `n`, con

\[
L(1,\chi_n)\ge c_s n^{-\delta/2}.
\]

La cota elemental de divisores da un `c_\tau>0` con `τ(n)≤c_τn^{δ/4}`. Al sustituir ambas cotas en la desigualdad del recuadro y cancelar el factor positivo `n^{δ/2}`, queda

\[
r_3(n)\ge\frac{c_s}{72c_\tau^2}n^{1/2-\delta}
\ge\frac{c_s}{72c_\tau^2}n^{1/2-\varepsilon}.
\]

La constante `c_s` es inefectiva, como en el teorema importado de Siegel. Esta ruta no proporciona un umbral universal expresado por un numeral evaluable.

## 6. Cierre del casquete libre de cuadrados

Aplicamos la cota inferior con `ε=η_K/2`. Si ningún punto estuviera en el casquete deseado, el polinomio núcleo tendría suma a lo sumo `ρ^K r₃(t)`. Su media y la elección de `K` obligarían entonces a

\[
\frac{r_3(t)}{2(K+1)}\le C_{u,K}t^{1/2-\eta_K}.
\]

La cota inferior hace que el lado izquierdo sea al menos una constante positiva por `t^{1/2−η_K/2}`. Al dividir por `t^{1/2−η_K}`, se obtendría una cota superior fija para `t^{η_K/2}`, imposible para todos los `t` grandes. Esto demuestra H1 con el orden de cuantificadores de la sección 1.

## 7. Del caso libre de cuadrados a todos los radios

Se escribe `n=t m²`, con `t` libre de cuadrados. De `n≡3 (mod 8)` se deduce que `m` es impar y `t≡3 (mod 8)`.

Si `t` supera el umbral de H1, se aproxima la dirección con una representación de `t` y se multiplica por `m`. Si `t` queda por debajo de ese umbral, sólo hay un conjunto finito de valores posibles: se fija una representación de cada uno mediante Gauss–Legendre y se aplican las rotaciones cuaterniónicas provenientes de H2. Al crecer `n` con esos `t` acotados, necesariamente crece `m`. Se puede tomar el máximo de los umbrales correspondientes al conjunto finito de representaciones fijadas.

Este paso es el teorema ya existente `threeSquaresDense_of`. H2 se suministra con `fourSquaresDense`, cuya prueba usa la identidad de Jacobi para radios impares y la construcción de cuatro cuadrados en casquetes. Los extremos del ensamblaje son `dukeSquarefree` y `threeSquaresDense`; sus declaraciones finales no toman H1, H2 ni los dos contratos analíticos como parámetros. El resultado de compilación y las consultas de axiomas están en `h1-recovery-20261108/REPORT.json` y `h1-recovery-20261108/AXIOMS_FINAL.log`.

## 8. Recuperación del respaldo y alcance de la comprobación

La ruta original comunicada, `C:/lean/three_squares`, no estaba disponible en este entorno. Se recuperó la rama privada `h1-wip` en `C:/nw/three-squares-h1-wip`, partiendo del commit `255becc069c6de3c44c1be44b7e512903868bc41`. El único remoto configurado es `backup`, dirigido al repositorio privado `jtraverso/three-squares-h1-wip`. La rama pública de Gauss–Legendre conserva su commit original.

El respaldo no incluía el paquete de cotas de Weil ni el cierre de importaciones de Siegel. Se restauraron con sus licencias y revisiones fijadas; el primero necesitó adaptar el sistema de módulos de Lean 4.34 a 4.35. Tampoco contenía las definiciones de `sigmaHalf` que usaba H2: se recuperaron de `four-squares-in-caps`, cambiando únicamente el espacio de nombres. El archivo original `DecompSum.lean` recibe esa importación y un nombre distinto para su lema auxiliar sobre divisores, que colisionaba con el lema de H1. Deshacer ambas reparaciones reproduce el archivo original. Los otros 141 archivos Lean originales se conservan idénticos.

La comprobación comprende el cierre completo de importaciones de `ThreeSquaresDenseProof` y los axiomas transitivos de los extremos, de los nuevos lemas y de los proveedores analíticos. Los archivos de desafío de Gauss–Legendre con marcadores `sorry`, así como los borradores que no se importan, quedan fuera de ese cierre. Los registros de intentos fallidos se conservan como diagnóstico; no se usan como certificados de éxito. No se afirma una prueba de la versión general de Duke–Schulze-Pillot para formas ternarias arbitrarias ni un umbral numérico efectivo.
