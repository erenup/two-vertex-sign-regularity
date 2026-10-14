# The two-checker-vertex theorem for nonsingular sign-regular intervals

## 1. Statement and notation

For an increasing row set I and column set J of the same size, write X[I,J] for the corresponding submatrix, with both index sets in increasing order. A real n-by-n matrix X is sign regular with signature epsilon=(epsilon_1,...,epsilon_n), epsilon_j in {+1,-1}, if

    epsilon_j det X[I,J] >= 0 whenever |I|=|J|=j.

Put epsilon_0=1. Zero minors are allowed. Let D=diag((-1)^1,...,(-1)^n). Write A<=*B if DAD<=DBD entrywise. The checker interval K between A and B is the entrywise box whose coordinate bounds are the corresponding entries of A and B. Its two opposite checker vertices are A and B.

**Theorem.** Suppose A<=*B, and A and B are nonsingular sign-regular real n-by-n matrices with the same signature epsilon. Then every X in K is nonsingular and sign regular with signature epsilon.

The proof applies to every n; in particular it proves the catalogue assertion for all n>=5. The case n=1 is immediate, so assume n>=2 below.

## 2. Unconditional interval facts

### 2.1 Nonsingularity throughout the box

We first prove an inverse-positive interval fact. Suppose P<=Q entrywise and P^{-1},Q^{-1} are nonnegative. Set

    v=P^{-1}1,  w=Q^{-1}1,  T=Q^{-1}(Q-P).

The vectors v,w are strictly positive because an invertible nonnegative matrix has no zero row. Also T>=0 and Tv=v-w<v. In the weighted maximum norm with weights v, the norm of T is max_i (Tv)_i/v_i<1. For P<=C<=Q put E=Q^{-1}(Q-C). Then 0<=E<=T, so ||E||<1. Since C=Q(I-E), its inverse is

    C^{-1}=(sum_{m>=0} E^m)Q^{-1}>=0.

For the theorem's endpoints put delta=epsilon_(n-1) epsilon_n. The cofactor formula for the inverse gives

    delta D A^{-1}D>=0,   delta D B^{-1}D>=0.

If delta=+1, apply the preceding fact to P=DAD,Q=DBD. If delta=-1, apply it to P=-DBD,Q=-DAD. This proves that every X in K is nonsingular. Its determinant has sign epsilon_n, by continuity and connectedness of K. The inverse cofactor formula also gives its prescribed order-(n-1) signs, although only nonsingularity will be needed in the induction below.

### 2.2 Staircase support of a nonnegative TP2 matrix

Here and below TP2 means that all order-two minors are nonnegative; it does not assert strict positivity. If Y is nonnegative, nonsingular and TP2, then every diagonal entry is positive. Indeed, nonsingularity supplies a permutation whose selected entries have positive product. If that permutation has an adjacent inversion, its two positive crossing entries and the nonnegative corresponding 2-minor force the two uncrossed entries to be positive. Repeatedly uncrossing reaches the identity permutation.

If Y_ij=0 with i<j, then every Y_rc with r<=i,c>=j is zero. First use the 2-minors on rows i,j and columns j,c, together with Y_jj>0, to obtain Y_ic=0 for c>=j. Then use rows r,i and columns i,c, together with Y_ii>0, to obtain Y_rc=0. Transposition gives the analogous southwest propagation for a zero below the diagonal.

Consequently each row and column has a contiguous nonempty interval of positive entries containing its diagonal position. The left and right endpoints of the row intervals are nondecreasing with the row index; this follows directly from the southwest and northeast zero propagation just proved. We call these properties staircase support.

### 2.3 Orders one and two throughout K

Order one is immediate. For order two we may first negate all matrices if necessary to make endpoint entries nonnegative, and reverse all rows if necessary to make their 2-minors nonnegative. Negation and row reversal multiply all minors of a specified order by one common sign and map checker intervals to checker intervals, possibly interchanging the endpoint names. Thus these normalizations do not lose generality.

On two consecutive rows and columns, ad-bc is increasing in a,d and decreasing in b,c. Its extrema over the box occur at the two checker vertices, so every adjacent 2-minor throughout K is nonnegative.

Take X in the relative interior of K. Its positive support is the union of the endpoint supports. This union has staircase support: each row's two endpoint intervals contain its diagonal, and their left and right boundaries remain nondecreasing after taking the union. If X_il and X_jk are positive, with i<j and k<l, the entire rectangle [i,j] times [k,l] is positive. Indeed every intermediate row has left support boundary at most k and right support boundary at least l. Multiplying all adjacent 2-minor inequalities in this rectangle and cancelling positive factors gives

    X_ik X_jl >= X_il X_jk.

If either crossing entry is zero, this inequality is immediate. Hence all 2-minors of X are nonnegative. Continuity proves the same on the boundary of K. Undoing the normalizations proves the prescribed order-two signs. In particular, whenever a nonsingular interval matrix or a Schur matrix below is normalized to have nonnegative entries and nonnegative 2-minors, it has the staircase support of Section 2.2.

## 3. Two structural lemmas for nonsingular nonnegative SR matrices

Let Y be a nonnegative nonsingular N-by-N matrix, with all 2-minors nonnegative and all 3-minors of weak sign eta, where eta is +1 or -1. We use these lemmas only for N>=3.

### 3.1 A positive zero-two anchor lies in a unique rank-one corner

Suppose the minor on rows i<j and columns k<l is zero and all its four entries are positive. Then one of the following rectangles has rank one:

    eta=-1: [1,j] x [1,l] (NW), or [i,N] x [k,N] (SE);
    eta=+1: [1,j] x [k,N] (NE), or [i,N] x [1,l] (SW).

Moreover, for the specified indices and eta, the permitted orientation is unique.

To prove this, divide rows i and j by their positive column-k entries, writing the resulting rows as u,v. Then u_k=v_k=1 and u_l=v_l=rho>0. Put d_t=v_t-u_t. Order two gives

    d_t<=0 for t<k;  d_t=0 for k<=t<=l;  d_t>=0 for t>l.

For another row h put q_h=Y_hl-rho Y_hk. Order two gives q_h<=0 for h<i, q_h=0 for i<=h<=j, and q_h>=0 for h>j. Some q_h is nonzero, since columns k,l of Y are independent.

Subtracting the normalized row u from v shows that the 3-minor on rows (h,i,j), h<i, or (i,j,h), h>j, and either ordered column set (t,k,l), t<k, or (k,l,t), t>l, equals

    -d_t q_h.

Only the two positive row normalizations have been omitted from this determinant. The formula remains valid when row h has zero entries at k or l. If both an earlier q_h<0 and a later q_h>0 existed, the required sign eta would force d_t=0 on both outer column ranges. Rows i,j would be proportional, contrary to nonsingularity. Thus strict q_h occur on exactly one side.

Suppose there is a later strict row h>j. Then q_r=0 for every r<=j. For every such r with Y_rk>0, the same determinant identity applied to rows r,j and the later row h shows that row r is proportional to row j on columns >=k if eta=+1, and on columns <=l if eta=-1.

If r<=j has Y_rk=0, then Y_rl=0 as well. Staircase support and Y_jk>0 imply r<k, r<i, and that row r is zero in every column >=k. For eta=+1 these are simply zero rows of the NE corner. For eta=-1 they are impossible: at t=r<k, the 3-minor on rows (r,i,h), columns (t,k,l), is

    Y_rr det Y[(i,h),(k,l)] >0,

contrary to eta=-1. Therefore the asserted NE or NW corner has rank one. Reversing both rows and columns preserves every minor sign and proves the two bottom-attached cases.

For uniqueness, a p-by-q submatrix of an invertible N-by-N matrix has rank at least p+q-N, because adjoining its missing rows and columns can increase rank by at most 2N-p-q. Thus a rank-one corner has p+q<=N+1. For eta=-1, NW requires j+l<=N+1 whereas SE requires i+k>=N+1; these cannot both hold since i+k<j+l. For eta=+1, NE requires j<=k whereas SW requires l<=i, again incompatible. This proves uniqueness.

### 3.2 Negative third-order sign permits zeros only at two corner entries

Suppose eta=-1. Then the only possible zero entries of Y are (1,N) and (N,1).

Indeed, let Y_ij=0 with i<j. Its northeast rectangle is zero by staircase support. If N-j+1>=2, take two independent columns with indices >=j. They vanish on all rows <=i, so some 2-minor on rows >i is nonzero, hence positive. Appending row i and column i gives a positive 3-minor, since Y_ii>0 and the two appended top-right entries vanish. This is impossible. Hence j=N.

Likewise, if i>=2, take two independent rows with indices <=i. They vanish on all columns >=j, so some 2-minor on columns <j is positive. Appending row j and column j gives a positive 3-minor, again impossible. Thus i=1. Transposition handles zeros below the diagonal; diagonal zeros are already excluded. The two possible zero positions are therefore exactly as asserted.

## 4. Signed Schur complements

Let Z be a nonsingular matrix, and let P,Q be row and column sets of the same size p such that H=Z[P,Q] is nonsingular. Empty sets are allowed: for p=0 use det H=1 and the empty Schur elimination. The Schur complement, with complementary indices retained in increasing order, is

    S_Z=Z[P^c,Q^c]-Z[P^c,Q] H^{-1} Z[P,Q^c].

For i not in P and j not in Q put

    alpha_i=(-1)^(number of elements of P greater than i),
    beta_j =(-1)^(number of elements of Q greater than j).

The bordered-minor formula is

    det (diag(alpha) S_Z diag(beta))[I,J]
       = det Z[P union I,Q union J] / det H.                 (4.1)

It follows by eliminating the pivot block H in the bordered submatrix; the factors alpha,beta undo exactly the permutations that put appended rows and columns into increasing order. The same block elimination also proves the rank identity

    rank Z[U,V]=p+rank S_Z[U minus P,V minus Q]               (4.2)

whenever U contains P and V contains Q. In particular S_Z is nonsingular.

Suppose the minors of Z needed in (4.1) have their prescribed signs epsilon. Normalize the Schur matrix by

    T_Z=(epsilon_p epsilon_(p+1)) diag(alpha) S_Z diag(beta).

Its entries are nonnegative. Its order-two sign is epsilon_p epsilon_(p+2), and its order-three sign, when prescribed, is epsilon_(p+1) epsilon_(p+3). Reverse all Schur rows if the order-two sign is negative. The resulting normalized Schur matrix is nonnegative and TP2; its prescribed third-order sign is

    delta_p=epsilon_p epsilon_(p+1) epsilon_(p+2) epsilon_(p+3).  (4.3)

For a matrix whose lower minors are already known to have their prescribed signs, the nonnegativity and TP2 assertions require only orders p+1 and p+2. No assertion about its order p+3 is being assumed. A wrong-sign bordered (p+3)-minor corresponds by (4.1) to a wrong-sign 3-minor of this normalized Schur matrix.

The Schur matrices of two checker-comparable matrices need not be checker-comparable. No such comparison will be used.

## 5. Interior zeros, Fekete propagation, and essential lines

### 5.1 A relative-interior zero of a correctly signed minor is permanent

Suppose all minors through order k-1 have their prescribed weak signs everywhere on K. A determinant is multi-affine in the genuinely variable scalar coordinates of the box. At a relative-interior point, repeated scalar interpolation expresses its signed value as a weighted average of its signed values at all box vertices, with every weight strictly positive.

Consequently, if such a signed minor vanishes at a relative-interior point, it vanishes identically on K. In particular, if a submatrix has rank s<=k-2 at that point, its rank is at most s everywhere on K. Its rank at a relative-interior point is therefore its maximum rank over K.

### 5.2 The exact three-term Fekete identity

Fix k rows R and a (k-1)-element subset R' of R. Write a k-column set as J={a} union S union {c}, where a=min J,c=max J and |S|=k-2. Let a<b<c with b not in J. Write Delta(T)=det Z[R,T] and d(T)=det Z[R',T], always sorting column sets. Then

    Delta(J) d(S union {b})
      = Delta((J minus {a}) union {b}) d(S union {a})
        + Delta((J minus {c}) union {b}) d(S union {c}).      (5.1)

For completeness, apply the cofactor-kernel identity to the k-by-(k+1) matrix on columns J union {b}. Restrict its vector identity to rows R', then apply the linear functional that appends that vector after the k-2 fixed columns S and takes the determinant. All terms indexed by S vanish. If b is in position t of the k+1 columns, the three remaining signs, for a,b,c, are (-1)^(k-1),(-1)^k,(-1)^(k+1). Rearrangement gives (5.1). The cofactor-kernel identity itself is Laplace expansion with a repeated row, so no rank hypothesis is needed.

If all (k-1)-minors have one common weak sign and d(S union {b}) is nonzero, dividing (5.1) expresses Delta(J) as a nonnegative linear combination of two k-minors with smaller column span.

### 5.3 A minimal bad minor supplies a rank-(k-2) interior rectangle

Continue to assume all orders <=k-1 are correct throughout K. Every solid k-minor, meaning consecutive rows and consecutive columns, is correct too. Indeed its derivatives in global checker coordinates are its signed (k-1)-cofactors times one common parity factor. Thus its signed determinant is monotone in one common checker direction throughout K, and its minimum is attained at A or B.

If a bad k-minor exists, it exists at a relative-interior matrix M by continuity. Among the bad k-minors at M choose one minimizing the sum of row span and column span. Since solid k-minors are correct, at least one index set has a gap. Transpose first if necessary so that its column set J has a gap. Write

    J={a} union S union {c},  |R|=k,  |S|=r=k-2,
    C={a+1,...,c-1}.

Then |C|>=k-1=r+1 and

    rank M[R,C]=r.                                          (5.2)

To prove this, the bad determinant is nonzero, so the r columns S on R are independent. If any omitted interior b increased their rank to r+1=k-1, some R' would give a nonzero denominator in (5.1). Its two smaller-span minors have the correct sign by minimality, a contradiction. Hence every interior column lies in the span of S, proving (5.2). By Section 5.1 this rank bound holds throughout K.

### 5.4 A free entry lies in an essential row or column

A row or column of a rank-r matrix is essential if deleting it reduces the rank to r-1. If rank(F+t E_ij)<=r for all sufficiently small positive and negative t, then row i or column j of F is essential.

Indeed every r-minor after deleting row i and column j must vanish; otherwise it would be the nonzero coefficient of t in a forbidden (r+1)-minor. Factor F=UV with U of full column rank r and V of full row rank r. If neither line were essential, deleting row i from U and column j from V would leave both ranks equal to r, so their product would have rank r, contrary to that vanishing.

Apply this to F=M[R,C] in (5.2). If the rectangle is not fixed throughout K, a genuinely variable entry supplies such a two-sided variation at M, so an essential row or column exists. After deleting that line its rank at M is r-1; by Section 5.1 the residual rectangle has rank at most r-1 at both endpoints as well.

## 6. Two further elementary consequences

### 6.1 A negative TP2 3-minor has a positive middle column

A nonnegative 3-by-3 matrix with nonnegative 2-minors and a zero in its middle column has nonnegative determinant. Write its rows as (a,b,c),(d,e,f),(g,h,i). If e=0, the two relevant 2-minors give bd=fh=0, and its determinant is bfg+cdh>=0. If b=0 and e>0, the upper-right 2-minor forces c=0, and the determinant is a(ei-fh)>=0. If h=0 and e>0, the lower-left 2-minor forces g=0, and the determinant is i(ae-bd)>=0. These cases exhaust the middle-column zeros.

### 6.2 A rank bound when the Schur third-order sign is negative

Fix 3<=k<=n and put p=k-3. Suppose an endpoint Z has

    epsilon_p epsilon_(p+1) epsilon_(p+2) epsilon_(p+3)=-1.

Let a rectangle Z[R_0,C_0] have rank t<=p, with |R_0|>=p. Choose t columns of C_0 forming a basis on R_0. Because the full rows R_0 of the nonsingular matrix Z are independent, extend these to p independent full-matrix columns on R_0. Every added column can be chosen outside C_0, since all columns of C_0 already lie in the initial span. Call the p chosen columns L. Choose p rows P_0 subset R_0 making Z[P_0,L] nonsingular.

Every column of C_0 is a linear combination of the initial t columns on all of R_0. Therefore the Schur complement at this pivot is zero on

    (R_0 minus P_0) x (C_0 minus L),

a rectangle of size

    (|R_0|-p) by (|C_0|-t).                                 (6.1)

The normalized Schur matrix is nonnegative, nonsingular, TP2, and has nonpositive 3-minors by (4.3). Section 3.2 permits only two zero entries in that whole matrix. Thus (6.1) cannot contain three or more entries.

In particular a rectangle of rank at most p cannot have either of the following sizes:

    at least (p+2) by (p+2), or at least (p+3) by (p+1).      (6.2)

In the first case (6.1) has at least 2 by 2 entries; in the second at least 3 by 1. Empty pivots when p=0 are covered by the same argument.

## 7. Induction: exclusion of every bad k-minor

Orders one and two are proved in Section 2. Assume all orders through k-1 are proved, where 3<=k<=n. Suppose a bad k-minor exists, and use the notation M,R,J={a} union S union {c},C,r=k-2 of Section 5.3. Put p=r-1=k-3 and

    delta=epsilon_p epsilon_(p+1) epsilon_(p+2) epsilon_(p+3).

We treat fixed and nonfixed interior rectangles separately.

### 7.1 The interior rank-r rectangle is fixed

The r selected columns S on R are independent. Choose an invertible p-by-p pivot H=M[P,Q] with P subset R,Q subset S. For p=0 use the empty pivot. It is fixed throughout K. Form the normalized Schur matrices T_A,T_B,T_M of Section 4, using the same pivot positions, signs, and row reversal. All are nonsingular, nonnegative and TP2. The endpoint third-order sign is delta, and the bad k-minor becomes a wrong-sign 3-minor of T_M.

Its selected rows are the three rows R minus P, possibly in reversed order, and its selected columns are a,q,c, where q is the unique element of S minus Q. On those three rows and all columns C minus Q, the Schur matrices share a fixed rank-one block. This follows from (4.2), and its column q is nonzero. There are at least two such interior columns. The outer columns a and c survive and lie on opposite sides of all of them in the full Schur column order.

If delta=-1, every entry of an interior column of T_A or T_B is positive by Section 3.2. Thus the shared rank-one block is positive.

If delta=+1, the target 3-minor is negative, so Section 6.1 makes all three entries of its middle column q positive. Any other nonzero column of the shared rank-one block is consequently positive on the same three rows. If there is no such second nonzero column, choose another interior column b, which is zero on those rows. Staircase support of T_M implies that when b<q all three rows are zero at outer column a, and when b>q all three are zero at outer column c. Either gives a zero target determinant, a contradiction.

We therefore have, in both cases, column q and at least one other positive column of the shared rank-one block. Choose q and one such other column as the two anchor columns. Apply Section 3.1 to these columns and the first and last of the three selected rows. At each endpoint this positive zero-two anchor lies in a rank-one corner. Its orientation is the same at both endpoints, by uniqueness. The corner contains all three selected rows and reaches either the left or the right column boundary. It therefore contains one common outer column d in {a,c}, as well as column q.

Rank lifting through H now gives

    rank A[R,S union {d}]<=r,
    rank B[R,S union {d}]<=r.                                (7.1)

Every (r+1)-minor in this rectangle vanishes at both endpoints. The columns S are fixed, so each such determinant that uses d is affine in the entries of column d. It therefore vanishes at the midpoint (A+B)/2. Those not using d are already zero. The midpoint is a relative-interior point of K, and r+1=k-1 is an already-correct order. Section 5.1 makes these zeros permanent throughout K.

Thus rank M[R,S union {d}]<=r. Adjoining the other outer column raises rank by at most one, so the purported bad k-minor has rank at most r+1=k-1. This contradicts its nonzero determinant. The fixed case is impossible.

### 7.2 The rectangle has a free entry and delta=-1

Section 5.4 supplies an essential row or column, whose deletion leaves a rectangle of rank at most r-1=p at both endpoints.

If it is a row, the residual dimensions are (k-1) by |C|, at least (p+2) by (p+2). If it is a column, they are k by (|C|-1), at least (p+3) by (p+1). Each contradicts (6.2) at either nonsingular SR endpoint. Hence this case is impossible.

### 7.3 The rectangle has a free entry and delta=+1

Again select an essential row or column. We now form a Schur complement at M only; its pivot need not be fixed or survive at the endpoints.

If row i of M[R,C] is essential, the restriction to rows R minus {i} and columns S has rank r-1. To see this, S is a column basis for the entire rectangle, so restricting to S preserves all its row relations. Choose a nonsingular p-by-p pivot with P subset R minus {i} and Q subset S. In the rank-one interior Schur block, the two remaining selected rows other than i are zero on every interior column outside Q. Thus the target 3-minor has zeros in its middle column. It is a nonnegative TP2 submatrix, so Section 6.1 excludes the required negative determinant.

If column j of M[R,C] is essential, every column basis S contains j. Take Q=S minus {j} and choose p rows P making the pivot nonsingular. Every other interior column belongs to the span of Q, so the interior Schur block is zero in all columns except possibly j. There is at least one such zero interior column b. The bad target 3-minor would be negative, forcing its middle column j to be positive on all three selected rows by Section 6.1. Staircase support then forces one outer target column to be zero, according as b<j or b>j. Its determinant is zero, again a contradiction.

All cases are impossible. This proves the order-k assertion at every relative-interior matrix. A bad boundary minor would persist after a sufficiently small motion into the relative interior, so none exists there either; equivalently one may use continuity for the weak inequalities. The induction is complete.

Every interval matrix is therefore sign regular with the original signature. Its nonsingularity was proved separately in Section 2.1. This proves the theorem.

## 8. Scope

The argument treats arbitrary real entries, all signatures, all zero-minor patterns, and every dimension in the theorem. In particular it does not assume strict sign regularity, positive endpoint entries, a fixed support, or checker comparability after Schur elimination.
