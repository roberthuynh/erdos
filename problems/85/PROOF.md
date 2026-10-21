# Rank-controlled projective-incidence rigidity by weighted chart transport

Written proof dated 16 October 2026. AI-written and AI-reviewed. The full stated theorem and corollaries were subsequently verified in Lean; no human mathematical review. Public priority is unresolved. This exposition retains the frozen mathematical argument. “Author claim” identifies its written-proof status, not a formal certificate.

## 1. The candidate theorem

Let `n>=2`, and let q and r be arbitrary prime powers. Let P and H be the points and hyperplanes of the supplied canonical `PG(n,q)`. Set

    N = (q^(n+1)-1)/(q-1),
    d = (q^n-1)/(q-1),
    lambda = (q^(n-1)-1)/(q-1),
    a = d-lambda = q^(n-1),
    m = N d.

Let

    phi : P -> points of PG(n,r),
    psi : H -> hyperplanes of PG(n,r)

be arbitrary fixed functions. Let T count original source flags `(p,H)` for which `phi(p)` is not on `psi(H)`, once each. Put `delta=T/m`.

An ordered projective frame consists of n+2 points, every n+1 of which are independent. Let rho be the fraction of uniform ordered source frames whose images under phi are target frames. Repeated image points fail.

For a field embedding `sigma:F_q -> F_r` and an invertible `(n+1)`-by-`(n+1)` target matrix A, let G be the point embedding

    [v] -> [A sigma(v)]

and its ONE coupled hyperplane embedding. Equivalently, the hyperplane image is the F_r-linear span of the images of its source points. Let D(G) count the total changed point and hyperplane entries.

**Theorem, author claim.** If

    rho>0,                    delta <= rho/(10^9 n^2),       (1.1)

then a field embedding `F_q -> F_r` exists, and there is one such coupled G with

    D(G) <= 5 T/q^(n-1) <= 10 T/d.                         (1.2)

Consequently every pair of arbitrary functions satisfies the dichotomy

    some coupled semilinear embedding G has D(G)<=10T/d,
    OR
    rho <= 10^9 n^2 delta.                                 (1.3)

In particular (1.3)'s second alternative holds if the source field does not embed in the target field. The first alternative does not assume that the two fields have equal cardinality or characteristic.

The proof below is self-contained apart from elementary finite-field and projective-space facts. The required additive correction and protected plane counting arguments are proved here. Their historical provenance and classical antecedents are recorded in [DEPENDENCIES.md](DEPENDENCIES.md) and [SOURCES.md](SOURCES.md).

## 2. A weighted protected-plane lemma

We first work in `PG(2,q)` and `PG(2,r)` with arbitrary point and line functions. Normalize the following seven point values and six line values to agree in their respective field coordinates:

    U=[1:0:0], V=[0:1:0], O=[0:0:1], I=[1:1:1],
    W=[1:1:0], E=[1:0:1], J=[0:1:1];
    infinity, d_0:y=x, v_0:x=0, v_1:x=1,
    h_0:y=0, h_1:y=1.

This is the baseline protected plane configuration. The new weighting will use specified flag distributions, not the unweighted total error of this plane.

Write `b(p,l)` for the indicator of a broken plane flag. Put

    v_x: x-coordinate=x,       h_y: y-coordinate=y,
    d_b: y=x+b,                l_a: y=ax,
    l_(a,b): y=ax+b.

The cost eta is the sum of the following twenty-four normalized sums of broken-flag indicators. A row with two displayed flags means TWO separate sums. A one-, two-, or three-parameter sum is divided by q, q^2, or q^3 respectively. For a restricted parameter `a!=0`, keep the denominator q or q^2, rather than q-1 or q(q-1).

| Number of sums | Parameters | Flags in the sums |
|---|---|---|
| 2 | x, respectively y | `(V,v_x)`, `(U,h_y)` |
| 2 | x,y | `((x,y),v_x)`, `((x,y),h_y)` |
| 2 | t | `((t,t),v_t)`, `((t,t),h_t)` |
| 1 | t | `((t,t),d_0)` |
| 1 | a!=0 | `(O,l_a)` |
| 1 | a!=0,t | `((t,at),l_a)` |
| 2 | a!=0 | `((1,a),v_1)`, `((1,a),h_a)` |
| 2 | a!=0 | `((a^-1,1),v_(a^-1))`, `((a^-1,1),h_1)` |
| 2 | a!=0 | `((1,a),l_a)`, `((a^-1,1),l_a)` |
| 1 | b | `(W,d_b)` |
| 1 | x,b | `((x,x+b),d_b)` |
| 4 | b, separately i=0,1 | `((i,i+b),v_i)`, `((i,i+b),h_(i+b))` |
| 2 | b, separately i=0,1 | `((i,i+b),d_b)` |
| 1 | a,b,x | `((x,ax+b),l_(a,b))` |

The entries in the first column sum to 24. Repetitions among these flag families are intentional and counted. The inequalities below remain valid if b is replaced in this cost by any nonnegative function that dominates b pointwise.

Define

    B_X = {x : (V,v_x) is broken},
    X   = {x not in B_X : psi(v_x) is not infinity},
    X_0 = F_q minus (B_X union X),

and analogously `B_Y,Y,Y_0` using `(U,h_y)`. For x in X, define f(x) by the proper vertical image `x=f(x)`; for y in Y define g(y) by the proper horizontal image `y=g(y)`. Extend both functions by zero at all other inputs. The normalized protected values give

    0,1 in X intersect Y,
    f(0)=g(0)=0,              f(1)=g(1)=1.                  (2.1)

**Weighted plane lemma.** If `eta<=10^-7`, there is a field embedding `sigma:F_q -> F_r` such that

    q-|X| <= 17 eta q,       q-|Y| <= 17 eta q,
    #{x:f(x)!=sigma(x)} <= 288 eta q,
    #{y:g(y)!=sigma(y)} <= 648 eta q.                      (2.2)

The affine point function agrees with `(sigma(x),sigma(y))` outside at most `971 eta q^2` points. No injectivity or noncollapse promise is imposed on the input functions.

### 2.1. Weighted support estimates

Let Q be the set of affine points at which the point-vertical or point-horizontal flag is broken. Write `x=|X|`, `y=|Y|`, and `b_X=|B_X|`, `b_Y=|B_Y|` only within this subsection.

At a point outside Q, intersecting its two preserved image coordinate lines gives:

    coordinates in X,Y:       image=(f(u),g(v));
    coordinates in X,Y_0:     image=V;
    coordinates in X_0,Y:     image=U.

For the diagonal, let Q_diag count its affine points in Q, and let e_diag count its broken affine point-diagonal flags. The target diagonal contains neither U nor V. Therefore

    |X symmetric-difference Y| <= b_X+b_Y+Q_diag+e_diag
                                <= eta q.                 (2.3)

The last inequality uses exactly the first, third, and fourth groups of weighted sums. The two sums defining Q_diag dominate its union count.

For a!=0 define

    r_a = #{t in X : at in Y_0},
    s_a = #{t in X_0 : at in Y}.

Let e_O count broken `(O,l_a)` flags with a!=0, and let E_pen count broken `((t,at),l_a)` flags over a!=0,t. If the O-flag is good, the image of l_a contains O and cannot contain both U and V. Thus at least `min(r_a,s_a)` of the indicated mixed points must be in Q or have a broken l_a flag. All mixed points here have both coordinates nonzero, so each lies on a unique such pencil line. On a broken O-flag use the upper bound q. Hence

    sum_(a!=0) min(r_a,s_a) <= q e_O + |Q| + E_pen
                            <= eta q^2.                   (2.4)

The q-fold use of a broken O-anchor flag is explicit in (2.4); its weighted cost is e_O/q. The Q and E_pen terms have their own normalized sums.

Including bad coordinates first gives

    |r_a-s_a| <= ||X|-|Y|| + b_X+b_Y <= 2 eta q.

It follows from (2.4) that `sum r_a <=3 eta q^2`. Every pair in `(X minus {0}) times Y_0` has exactly one nonzero slope, so

    (x-1)(q-y-b_Y) <= 3 eta q^2,
    (x-1)(q-y) <= 4 eta q^2.                               (2.5)

For each a!=0 with `a in Y_0` and `a^-1 in X_0`, consider

    P_a=(1,a),                 Q_a=(a^-1,1).

They lie on l_a and have images V and U unless in Q. Unless one of their l_a flags or the O-flag is broken, this is impossible. Let R_Q count appearances in Q in these two parameterized point families, and R_F count their broken l_a flags. Then the number of these slopes is at most

    e_O+R_Q+R_F.

Each of R_Q's two union counts is dominated by its TWO explicitly listed coordinate-flag sums. All other nonzero a belong to Y or B_Y, or have inverse in X or B_X. Consequently

    x+y >= q+1-(b_X+b_Y+e_O+R_Q+R_F)
          >= q+1-eta q.                                   (2.6)

There is no exceptional reciprocal degeneracy: a=1 is not in the displayed bad set because 1 belongs to X and Y.

If q=2, (2.1) already gives X=Y=F_q. If q>=3, (2.3), (2.6), and `eta<=1/12` imply

    x-1 >= (q-1-2 eta q)/2 >= q/4.

Together with (2.5), this proves

    q-y <= 16 eta q,         q-x <= 17 eta q.              (2.7)

Thus both bounds in the first line of (2.2) hold for every q, including q=2. These are real-number inequalities on integer counts; no positive rounding remainder is added.

### 2.2. Pexider correction with the protected values retained

The product identity holds outside at most

    K <= q(q-|X|)+q(q-|Y|)+|Q| <= 35 eta q^2               (2.8)

affine points. For d_b define c(b) as its target intercept when its W-flag is preserved and its image is proper affine, and as zero otherwise. Its slope in the proper case is 1, since W is fixed. In particular c(0)=0.

Let R count failures of

    g(u+b)=f(u)+c(b).

A product exception is used once, a broken W-anchor flag at most q times, and a point-diagonal flag once. The table includes the latter two families. Thus

    R <= K + q e_W + E_diag <= 36 eta q^2,
    r_0 := R/q^2 <= 36 eta.                               (2.9)

For a FIXED i=0 or i=1, the vertical line is protected. On that column the product identity can fail only at second coordinates outside Y or at a Q-point. Adding the W-anchor and point-diagonal flags gives the separate fixed-row estimate

    #{b:g(i+b)!=f(i)+c(b)} <= 20 eta q,    i=0,1.          (2.10)

The actual bound from (2.7) and the table is at most 17 eta q; 20 is retained. This does not substitute the global K bound for a fixed-row count. Similarly, using the diagonal-specific table entries gives

    #{t:g(t)!=f(t)} <= 36 eta q.                          (2.11)

Here c(0)=0 is protected; at most `(q-|X|)+(q-|Y|)+Q_diag+e_diag` parameters can fail the diagonal product argument.

We record the inherited additive correction proof to ensure it applies to the cross-field codomain. If a function A on the additive group of F_q fails additivity on a fraction theta<1/6 of pairs, put `z_x(y)=A(x+y)-A(y)`. For fixed x, the additive equations at `(x+y,z)` and `(y,x+z)` give `z_x(y)=z_x(z)` except on at most 2theta of the independent pairs y,z. Thus z_x has a unique mode H(x) of mass at least 1-2theta. The identity

    z_(x+t)(y)=z_x(t+y)+z_t(y)

and the three mode bounds prove H additive, since 6theta<1. If A(x)!=H(x), at least 1-2theta of that row's additive equations fail. Therefore A differs from H on at most `2theta q` arguments.

Apply the Pexider equation at the four pairs

    (a+x,b+y), (a+x+y,b), (a,b+y), (a+y,b).

Each pair is uniform when a,b,x,y are uniform. Their subtraction and averaging give a translate `A(x)=f(a+x)-f(a)` with additive defect at most 4r_0. The preceding argument gives an additive H and a constant alpha with f equal to H+alpha outside at most `8r_0 q` arguments. After this correction, the original Pexider equation gives

    g(z)-H(z)=alpha+c(b)-H(b)

except on at most 9r_0 of independent pairs z,b. The largest atom beta of `c(b)-H(b)` has mass at least 1-9r_0. The left side differs from alpha+beta on at most `9r_0/(1-9r_0)<=18r_0` of the z. Hence

    f = H+alpha       outside at most 8r_0 q arguments,
    g = H+alpha+beta  outside at most 18r_0 q arguments,
    c = H+beta        outside at most 9r_0 q arguments.     (2.12)

This uses only addition in the codomain F_r. All required inequalities, including `4r_0<1/6` and `9r_0<1/2`, follow from eta<=10^-7.

For each i=0,1, at most `(20 eta+27r_0)q <=992 eta q<q` choices of b are excluded by (2.10) and the g,c exceptions in (2.12). Some b remains, and substitution gives

    f(i)=H(i)+alpha.

Using (2.1) yields alpha=0 and H(1)=1. In particular H is nonzero. Equation (2.11) and the f,g exceptions exclude at most `(36 eta+26r_0)q<=972 eta q<q` choices of t, so beta=0 as well. Thus no target translation remains hidden in the normalization, and the corrected coordinate functions are both H.

### 2.3. All slopes and the field embedding

The affine point function equals `(H(x),H(y))` outside at most

    Z_2 <= K+26r_0 q^2 <= 971 eta q^2.                    (2.13)

For all triples a,b,x, mark the triple if `(x,ax+b)` is a point exception or if its original plane flag on l_(a,b) is broken. Each exceptional affine point is used exactly q times. The last table family bounds the broken-flag count, so

    M <= q Z_2 + eta q^3 <= 972 eta q^3 < q^3/4.           (2.14)

Let

    K_0 = {a in F_q : H(ax)=s H(x) for all x,
                      for some s in F_r}.

The scalar is unique because H is nonzero. If a is outside K_0, no target line contains more than q/2 entries of the parameterized list

    (H(x), H(ax+b)),          x in F_q.

A vertical line gives a fiber of the nonzero additive map H; a nonvertical line gives a fiber of the nonzero additive map `H(ax)-sH(x)`; the infinity line contains none. A nonzero additive map on a group of size q has every fiber of size at most q/2. This includes repeated list values. Every unmarked parameter lies on the actual image of l_(a,b), whichever target line that is. Thus each such a and each b require at least q/2 marks. By (2.14),

    |F_q minus K_0| <= 2M/q^2 < q/2.

K_0 is a subfield of F_q. It contains 0,1; addition and multiplication follow from the scalar identities. For a!=0 in K_0 its scalar is nonzero, since multiplication by a is surjective and H is nonzero. Substituting a^-1 x proves inverse closure. A proper subfield is a proper additive subgroup and has at most q/2 elements. Hence K_0=F_q. The unique scalars form an injective unital field homomorphism sigma to F_r, and

    H(x)=sigma(x)H(1)=sigma(x).

The f,g bounds in (2.12) and (2.9) are `288 eta q` and `648 eta q`, proving the weighted plane lemma. The field embedding, rather than input injectivity, is the conclusion.

## 3. Protecting a higher-rank frame with at most 7n^2 original flags

Let a source full frame be normalized to

    E_0=[e_0], ..., E_n=[e_n],      I=[e_0+...+e_n].

If it survives, normalize its target images independently to the corresponding target frame. Such a projective normalization exists: the first n+1 representatives form a basis, and all coefficients of the last point are nonzero, so rescaling the basis makes them all 1. This is also valid in characteristic 2.

Use homogeneous coordinates X_0,...,X_n and define

    H_0: X_0=0,
    H_i(0): X_i=0,
    H_i(1): X_i=X_0,                 1<=i<=n.

Protect H_0 and the n hyperplanes H_i(0) by their n basis-point flags each. Protect H_i(1) by the flags of I and the n-1 basis points E_k with k outside {0,i}. This costs

    n(n+1)+n^2 = 2n^2+n

original flags and forces all these hyperplane images exactly: their named target points are n independent points.

For each j=2,...,n, let A_j be the source coordinate plane spanned by E_0,E_1,E_j, and let B_j be the complementary vector subspace spanned by all e_k with k outside {0,1,j}. Its vector dimension is n-2. When n=2 it is the zero subspace; all statements about it then have their evident empty meaning.

Protect the following additional objects for this plane:

1. `S_j=[e_0+e_1+e_j]`: protect its incidences with H_k(0) for k outside {0,1,j}, and with H_1(1), H_j(1). These n hyperplanes have exactly that common target point, forcing phi(S_j).
2. `D_j: X_j=X_1`: protect its flags at E_0, S_j, and the n-2 complementary E_k. These n image points are independent in that target hyperplane, forcing psi(D_j).
3. `W_j=[e_1+e_j]`: protect its n flags with H_0, D_j, and the n-2 complementary H_k(0).
4. `E_j^*=[e_0+e_1]`: protect its n flags with H_j(0), H_1(1), and the n-2 complementary H_k(0).
5. `J_j^*=[e_0+e_j]`: protect its n flags with H_1(0), H_j(1), and the n-2 complementary H_k(0).

Each point in steps 3-5 is the unique intersection of the displayed target hyperplanes. This costs at most 5n flags per plane. Repeated flags and repeated points across planes are harmless; they remain counted slots. The total number of slots is

    M_cert = 2n^2+n+5n(n-1) = 7n^2-4n <= 7n^2.           (3.1)

Call a surviving full frame protected when all these ORIGINAL flags are good. For every j, its plane A_j then has the seven point values and six extended-line values of the protected configuration in Section 2. No injectivity of any other point value has been assumed.

## 4. The intrinsic chart transport lemma and its load

Fix a protected full frame. Use the corresponding target coordinate plane A'_j and complementary vector subspace B'_j. A source line l in A_j extends to the source hyperplane

    widehat(l) = vector-span(B_j,l).

Define a genuine point function from the source plane to the target plane by retaining phi(p) when it lies in A'_j, and replacing it by E_0 otherwise. Define a genuine line function by

    psi(widehat(l)) intersect A'_j,

when psi(widehat(l)) contains B'_j, and by the target infinity line of A'_j otherwise. In the first case the intersection is exactly a line: a hyperplane containing both B'_j and all of A'_j would contain the entire target vector space, since their direct sum is that space.

For a source plane flag (p,l), define its ORIGINAL error majorant

    U_j(p,l) = b_original(p,widehat(l))
             + sum_(k outside {0,1,j}) b_original(p,H_k(0))
             + sum_(k outside {0,1,j}) b_original(E_k,widehat(l)).  (4.1)

This uses exactly `1+(n-2)+(n-2)=2n-3` valid original flags, counted with their multiplicities.

If all flags in (4.1) are good, the middle group forces phi(p) into A'_j because all H_k(0) are protected. The last group forces psi(widehat(l)) to contain B'_j, because the complementary E_k are frame points with fixed images. The first flag then gives incidence of the retained point with the intersected line. Therefore the induced broken-flag indicator is at most U_j, pointwise.

This pays both possible failures that an unqualified restriction or quotient would miss: a point might leave the intended plane, and a hyperplane might fail to contain the complementary span. Neither is discarded for free.

The protected full-frame certificate forces the induced seven point and six line values to be the normalized configuration of Section 2. Let eta_j be its twenty-four-sum cost, using U_j in place of the induced indicator. The weighted plane lemma applies whenever eta_j<=10^-7.

### 4.1. Exact shared-pencil property

For each i=1,...,n, use the GLOBAL coordinate hyperplane pencil

    H_i(t): X_i=t X_0,              t in F_q.

Call t proper if its image hyperplane contains every E_k with k outside {0,i} and is not H_0. Such an image is necessarily `X_i=f_i(t)X_0`; define f_i(t) by this scalar. At nonproper inputs define f_i(t)=0. The protected values give proper inputs 0 and 1 and f_i(0)=0, f_i(1)=1.

For the induced plane A_j, the proper vertical-coordinate set is EXACTLY this global proper set for i=1, and its f is exactly f_1. Its proper horizontal-coordinate set is exactly the global proper set for i=j, and its g is exactly f_j.

To check this claim, if a complementary flag fails, the induced line is set to infinity and is not proper. If all complementary flags hold, the remaining local infinity-anchor flag holds precisely when the image hyperplane contains the remaining basis direction required by the global definition. Such a hyperplane meets A'_j in the proper local coordinate line unless it is H_0. Conversely, if that intersection is the local infinity line, its span with B'_j is H_0, so the original image hyperplane equals H_0. At nonproper inputs both extensions are zero. Thus no independently chosen extension or corrected anchor is hidden in the comparison.

## 5. All transport costs are counted before frame conditioning

Let F be a UNIFORM ordered full source frame, regardless of its image. Source projective linear transformations act transitively on these frames, and on original point-hyperplane flags. Every certificate slot and every flag in (4.1), at every fixed choice of the field parameters in the table, is a fixed projectively equivariant construction from F. Consequently EACH such original-flag slot is uniform on the m original flags before conditioning. Its expected error is delta.

Equivalently, if the number of ordered full frames is F_count, each fixed slot takes a given original flag exactly `F_count/m` times. This is a multiplicity identity before any good-image selection. No assertion of conditional uniformity is used.

Define U_j and eta_j for every source frame by their raw source formulas in (4.1) and the table, even when its image fails or its certificate is broken. These nonnegative raw costs do not require a target normalization to be evaluated. Each table sum has normalized mass at most 1. Therefore

    E[eta_j] <= 24(2n-3) delta.                            (5.1)

Also define the global product-coordinate cost

    gamma(F) = q^-n sum_(x in F_q^n) sum_(i=1)^n
                    b_original(p_x,H_i(x_i)),
    p_x=[e_0+x_1 e_1+...+x_n e_n].

Each of its n fixed-parameter flag families is equivariant and uniform in the same sense, so

    E[gamma] = n delta.

Put

    E_total(F) = gamma(F)+sum_(j=2)^n eta_j(F).

Then

    E[E_total] <= [n+24(n-1)(2n-3)]delta <= 48 n^2 delta.  (5.2)

The certificate fails with probability at most `7n^2 delta`, by its original slots and the union bound. Markov applied to (5.2) gives

    Pr(E_total>10^-7) <= 48*10^7 n^2 delta.

Thus the probability that the certificate fails OR E_total>10^-7 is at most

    (7+48*10^7)n^2 delta < 5*10^8 n^2 delta <= rho/2,      (5.3)

where the last step is (1.1). Since survival has probability rho>0, there exists a surviving protected full frame with

    E_total <= 10^-7.                                    (5.4)

If delta=0, every nonnegative cost in question is zero, and the same conclusion follows directly from rho>0. No division by zero occurs.

This is the rank-controlled noncollapse/transport selection. In particular, it never tries to detect higher-rank collapse by individual point or hyperplane fiber sizes.

## 6. One field embedding across every coordinate chart

Fix the frame from (5.4). Apply the weighted plane lemma to each A_j, using its majorant cost eta_j. By the exact shared-pencil property, the result is a field embedding `sigma_j:F_q -> F_r` with

    #{t:f_1(t)!=sigma_j(t)} <= 288 eta_j q,
    #{t:f_j(t)!=sigma_j(t)} <= 648 eta_j q,                (6.1)

and at most 17 eta_j q nonproper inputs in either pencil.

For any two charts j,k, their embeddings differ on at most

    288(eta_j+eta_k)q <= 288*10^-7 q < q/2

arguments, because each is close to the SAME f_1. If two additive maps are distinct, their difference is a nonzero additive map, whose kernel has size at most q/2. Hence two distinct field embeddings cannot agree on more than q/2 arguments. It follows that all sigma_j are the SAME field embedding sigma. For n=2 there is only one chart and this conclusion needs no comparison.

This proves scalar-field coherence explicitly; it is not an assertion that arbitrary plane corrections glue. The common first coordinate pencil is part of the original hyperplane data, before correction.

Let `eta_sum=sum eta_j`. For coordinate 1 choose chart j=2 once, and for coordinate j use its own chart. The sum of the numbers of nonproper inputs over all n coordinates is at most

    17(eta_2+eta_sum)q <= 34 eta_sum q.                    (6.2)

Likewise (6.1) bounds the sum of scalar-function disagreements with sigma by

    (288 eta_2+648 eta_sum)q <= 936 eta_sum q.             (6.3)

For an affine source point p_x, if all x_i are proper and its n point-coordinate-hyperplane flags are good, its image is the unique intersection of the n target hyperplanes

    X_i=f_i(x_i)X_0,               i=1,...,n.

That intersection is the affine point with those n coordinates. The union bound on coordinate values, now over the WHOLE affine chart, and the gamma count show that this product identity fails at at most

    (gamma+34 eta_sum)q^n

points. Correcting its n scalar coordinates using (6.3), the point map agrees with the ONE global affine embedding

    (x_1,...,x_n) -> (sigma(x_1),...,sigma(x_n))

outside at most

    Z <= (gamma+970 eta_sum)q^n <= 971 E_total q^n.        (6.4)

We retain the conservative constant 971. This is global agreement on the affine chart; it is not merely agreement on the union of the small coordinate planes. The embedding extends projectively to G, and its image of H_0 already equals psi(H_0).

## 7. Coarse paired agreement in general rank, including proper subfields

We use two elementary intersection bounds for a semilinear embedding G. A target hyperplane different from G(H) contains at most lambda images of source points of H. A target point different from G(p) lies on at most lambda images of source hyperplanes through p.

For completeness, normalize G to coordinatewise sigma. On the n-dimensional F_q vector space defining H, a different target hyperplane gives a nonzero sigma-linear functional into F_r. Its kernel has F_q-dimension at most n-1, hence at most lambda projective points. Dually, the F_q coefficient space of hyperplanes through p has dimension n. It spans the corresponding n-dimensional target coefficient space over F_r. A target point not equal to sigma(p) gives a nonzero sigma-linear evaluation on that space, again with kernel dimension at most n-1. Thus the same bound holds. These arguments use the F_r span, not target surjectivity or merely a zero F_q kernel.

A refinement for an AFFINE source hyperplane H gives at most q^(n-2) correctly embedded affine source points on a wrong target hyperplane. Its affine parameter space has F_q-dimension n-1. The restriction is either a nonconstant sigma-affine functional, with fibers at most q^(n-2), or a nonzero constant, with no zeros. A zero constant would make the target hyperplane contain the entire F_r span G(H), contradicting that it is different.

Let B be the number of wrong affine source hyperplanes, and let I_bad be the number of wrong source points on H_0. The affine point disagreement count is Z. A wrong affine hyperplane has q^(n-1)=a affine source points, and at most a/q correctly mapped ones can preserve their flags with its wrong image. Summing and charging each affine exception on its d source hyperplanes gives

    (a-a/q) B <= T+d Z.                                    (7.1)

A wrong infinity point lies on d-1 affine hyperplanes, at most lambda correctly mapped ones of which can contain its wrong image. Each wrong affine hyperplane contains lambda infinity points. Hence

    (a-1) I_bad <= T+lambda B.                             (7.2)

These are separate upper estimates using T; no disjointness of their errors is asserted or needed. Since

    d/a <= q/(q-1) <= 2,
    lambda/(a-1)=1/(q-1),
    a/(a-1)<=2,

(7.1)-(7.2) imply

    D(G)=Z+B+I_bad <= 9Z+6T/a.                             (7.3)

By (5.4), (6.4), q^n<=N, and `T/a<=2delta N`,

    D(G)/N <= 9*971*10^-7+12delta < 1/1000 < 1/20.        (7.4)

The strict numerical inequality uses `delta<=1/(10^9n^2)<=1/(4*10^9)`. This establishes entrywise proximity of BOTH original functions to the same G before the local sharpening.

## 8. The source-design local paired gap

This last lemma is valid for any coupled projective-semilinear embedding into PG(n,r), including a proper subfield embedding.

Let S and B_set be the wrong point and hyperplane sets relative to G, of sizes s,t, and let D=s+t. Write J_cross for their source incidence count. For a wrong point, at most lambda of all correctly mapped incident hyperplanes can contain its wrong image. The number of broken flags of type wrong point / correct hyperplane is therefore at least

    (d-lambda)s-J_cross = a s-J_cross.

The dual intersection bound gives at least `a t-J_cross` broken flags of type correct point / wrong hyperplane. THESE TYPES ARE DISJOINT. Consequently

    T >= aD-2J_cross.                                     (8.1)

The source point-hyperplane design has degree d, and every two distinct points lie together on lambda hyperplanes. Thus its incidence matrix satisfies

    A A^T = a Id+lambda AllOnes.

For n_H=|S intersect H|, this gives

    sum_H (n_H-ds/N)^2 = a s(1-s/N).

Center the indicator of B_set and apply Cauchy-Schwarz. Then

    J_cross <= d st/N
               +sqrt(a s(1-s/N)t(1-t/N))
            <= dD^2/(4N)+sqrt(a)D/2.

Together with (8.1),

    T >= [a-sqrt(a)-dD/(2N)]D.                            (8.2)

For a=q^(n-1)>=2, `sqrt(a)<=3a/4`. Also d<=2a. If D<=N/20, the coefficient in (8.2) is at least

    a-3a/4-2a/40 = a/5.

Apply this to (7.4). We obtain

    D(G)<=5T/a<=10T/d,

proving (1.2). Undoing the independent source and target frame normalizations leaves one map of the stated projective-semilinear form, with its coupled hyperplane action. All counts and Hamming distances are preserved.

## 9. Controls and exact limits of the claim

* For n=2, the complement and membership sums are empty. The transport cost is one original plane flag per induced flag, and there is one coordinate chart. The proof uses the protected-plane, reciprocal, Pexider and fixed-row arguments from Section 2 with weighted equivariant sampling.
* An exact projective-semilinear embedding, including a proper subfield embedding, has T=0, rho=1, and D=0. Its target frame images are independent over F_r because its underlying target matrix is invertible.
* Constant incident point and hyperplane maps have T=0 and rho=0. The positive survival hypothesis fails, as required.
* More generally, arbitrary point values in a proper target subspace W and arbitrary hyperplane values containing W can give exact incidence-preserving collapse. These have rho=0. The proof does not try to exclude them through individual fibers and is unaffected by the size of r.
* Starting with an embedding, move one source point p to the embedded image of a distinct source point b, retaining all other entries. Exactly lambda of the d incident source hyperplanes also contain b. Thus `T=d-lambda=q^(n-1)`, the paired distance to the original embedding is 1, and every source frame avoiding p survives. The correction scale T/d is therefore of constant order even as rank changes. This checks the exact source-degree normalization.
* If the characteristics differ, or q=p^u and r=p^v with u not dividing v, no field embedding exists. The theorem consequently forces `rho<=10^9n^2delta`. No unsupported full-rank extraction is used to infer this obstruction.
* The q=2 case is included explicitly in the support proof; all frame and hyperplane protections work in characteristic 2. No limiting argument or omitted small-field regime occurs.

The constants are not optimized. The theorem is existential, with no claimed efficient decoding algorithm or bit-complexity guarantee. The conclusion concerns this supplied canonical incidence family; it does not establish an original Erdos 85 extremal bound, an arbitrary non-Desarguesian target theorem, a general building theorem beyond the proved projective incidence statement, or public priority.
