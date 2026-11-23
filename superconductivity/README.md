# Verified shell dependence in a superconducting grain

Moving the outer shell from three to nine central level spacings lowers the
odd–even parity energy of a five-orbital reduced BCS grain at fixed bare
coupling. Lean derives the effective prediction from the occupation
Hamiltonians and checks an independently generated full-solve enclosure.

Let \(d\) be the central level spacing and \(g=d/1000\) the bare pair-transfer
strength. All numerical energies below use \(g\) as the unit. The parity
energy is \(\Delta_P=E_5-(E_4+E_6)/2\), where \(E_N\) is the ground
energy at exactly \(N\) electrons.

| Quantity | Result in units of \(g\) |
| --- | --- |
| Near spectrum | −3000, −1000, 0, 1000, 3000 |
| Far spectrum | −9000, −1000, 0, 1000, 9000 |
| Bare near-minus-far contrast | 0 |
| Second-order near-minus-far prediction | 1/9000 |
| Derived prediction interval, rounded outwards | [0.00010623598, 0.00011598659] |
| Full-Hamiltonian enclosure | [11129/100000000, 11141/100000000] |

The last row is \([0.00011129, 0.00011141]\), or
\([1.1129,1.1141]\times 10^{-7}d\) in spacing units. The same single-orbital
bare model gives parity energy \(g/2\) for either spectrum, for any common
central orbital energy and any frozen outer energy. The fixed-coupling
experiment probes a change in the outer orbital energies.

## Hamiltonian and effective prediction

The specified Hamiltonian is
\(H=\sum_{i,\sigma}\epsilon_i n_{i\sigma}-g\sum_{ij}b_i^\dagger b_j\),
where \(b_i\) annihilates a pair of time-reversed electrons. Each orbital
can be empty, singly occupied, or paired. A singly occupied orbital is
blocked. Its two spin assignments give identical copies of the same
Hamiltonian block. The pair operators on distinct orbitals have even fermion
degree, so a pair transfer has matrix element \(-g\) in this occupation
basis. The diagonal term counts the contribution \(-g\) of every occupied
pair. [Model in Lean](Grain/Model.lean)

The filling rule assigns up to two electrons to each orbital in increasing
energy order. Lean checks that this selects the unique kinetic minimum in
each of the six sectors. Let \(a\) be its Hamiltonian diagonal entry,
\(D_i\) the other diagonal entries, and \(b_i\) the couplings to the
reference. The reduction keeps \(b_i\) and drops hops between discarded
occupations. The maximum discarded row degree \(R\) is computed from
those hops. In coupling units, shifting the discarded diagonals by \(-R\)
or \(+R\) gives lower and upper bounds on the full quadratic form.

For either shifted diagonal, Lean derives the exact scalar Schur response
\(a-z-\Sigma_\pm(z)\), with
\(\Sigma_\pm(z)=\sum_i b_i^2/(D_i\pm R-z)\). Lean checks that the lower
pivot is positive at \(z=a\). Below \(a\) each correction increases with
\(z\), giving sector endpoints \(L=a-\Sigma_-(a)\) and
\(U=a-\Sigma_+(L)\). The second-order center evaluates the unshifted
correction at \(a\). The endpoints bound its error from the same matrix
entries and denominators. Propagating them through the signed parity
combination gives the prediction interval in the table.
[Scalar Schur proof](Grain/RankOne.lean) · [Effective reduction](Grain/Effective.lean) · [Prediction](Grain/Prediction.lean)

Lean reindexes the second-order sum by legal pair transfers. Every hop
from a filled negative level to an empty positive level has the same
denominator in all three sectors and cancels in parity. The remaining
hops vanish in the odd sector because the central orbital is blocked.
For a symmetric spectrum, the parity center is
\(\frac12+(1/1000+1/r)/2\) in coupling units. Its decrease with the outer
radius \(r>0\) picks the nearest and farthest candidate radii for the
largest second-order contrast. This is the finite-shell mechanism behind
the \(1/9000\) center.
[Cancellation proof](Grain/ParityCancellation.lean) · [Matveev & Larkin](https://arxiv.org/abs/cond-mat/9701041)

## Independent full solve

The Python generator consumes the frozen spectra and coupling, enumerates
the occupations at each particle number, and inserts the diagonal and
pair-transfer terms. It finds connected blocks of the resulting graph and
uses exact rational LDLᵀ bisection to locate each sector minimum. It emits
a positive lower-bound vector covering every occupation and a trial vector
for an upper bound. The solver shares the physical inputs with the prediction.
Its algorithm uses the primitive hopping rules and rational linear algebra.

Lean reassembles the Hamiltonian from its occupation model. It checks the
lower bound through a weighted quadratic-form inequality for all real
vectors and the upper bound through the trial vector's Rayleigh quotient.
Thus an arbitrarily chosen low-lying eigenpair cannot certify the result.
The matrices are real and symmetric, so the same extrema govern the complex
Rayleigh quotient by decomposing a complex vector into real and imaginary
parts. [Certificate soundness](Grain/Energy.lean) · [Generated witnesses](Grain/Certificate.lean) · [Headline theorem](Grain/Main.lean)

The original experiment froze the wider interval \([4/56250,17/112500]\)
before generating the full solve. Its design, sources and hashes preserve
that local record. The derived interval in the table is a later
revision checked against the existing full solve. The revision imports
only the occupation model and its reduction and variational lemmas.
The full-solve certificate has its own import closure. The hash audit checks
both records and the import dependencies.
[Original design](artifacts/design.json) · [Original sources](artifacts/five_orbital_original) · [Original hashes](artifacts/prediction.sha256.json) · [EFT revision hashes](artifacts/five_orbital_eft.sha256.json) · [Full-solve data](artifacts/certificate.json)

This result applies to a prescribed attractive reduced BCS model at zero
temperature. The sections below connect this prescribed attraction to a
synthetic harmonic electron–phonon Hamiltonian. The MgB₂ calculation below
uses independent electronic-structure data to identify the dominant static
pairing channel in a real crystal. [MgB₂ calculation](#which-couplings-dominate-in-mgb2)

## Exact elimination of two shells

For the seven-orbital spectrum \((-s,-r,-d,0,d,r,s)\), the fixed-number
occupation basis splits into three blocks. The retained block has both
shells filled below the Fermi level and empty above it. The second block
has a deviation in the inner shell only. The third has a deviation in the
outer shell. Each configuration appears exactly once.

At spectral parameter \(z\), shift the primitive Hamiltonian once to
\(M=H-zI\). For a retained block \(A\) and a discarded block \(D\), the
effective matrix is \(A-BD^{-1}C\). Lean proves that its action on a retained
vector is the full matrix response with the discarded rows set to zero.
When the pivot is nonsingular, the discarded amplitudes are uniquely
determined. Applying this characterization twice gives equality of the
successive and joint effective matrices.
[General composition proof](Grain/Schur.lean)

For \(0\le d\le r\le s\) and \(g\ge0\), the two eliminations are
valid throughout the explicit interval
\[
z < -2(d+r+s)+r-56g.
\]
Every discarded occupation costs at least \(r\) in kinetic energy relative
to the free reference. The diagonal pairing contribution has size at most
\(7g\), and the sum of off-diagonal magnitudes in each row is at most
\(49g\). Strict diagonal dominance therefore certifies the outer pivot
and the joint discarded block. The quotient identity then gives
nonsingularity of the second pivot. The constant \(56\) is a sufficient
bound obtained by allowing all ordered pairs of orbitals in the count.

The reduced equation has a nonzero solution exactly at a primitive
Hamiltonian eigenvalue in this interval. For \(N=6,7,8\), a normalized
trial state puts the variational ground energy inside the interval whenever
\(56g<r\), including \(g=d/1000\) with \(0<d\le r\).
The theorem supplies the exact energy-dependent baseline for bounding
approximations to two-step renormalization.
[Seven-orbital theorem and window](Grain/TwoShell.lean)

## A reduced model that survives both eliminations

Use \(g=d/100\), inner shell radii \(r/d\in\{2,5\}\), and outer radii
\(s/d\in\{6,14\}\). The mixed contrast is the difference between the two
inner-shell shifts in parity energy at the two outer-shell radii. The
central orbitals and bare coupling are common to all four spectra.

At a trial energy \(z\), split each discarded block as
\(D=L(I-T)\), where \(L\) is its diagonal. Replace \(D^{-1}\) by
\(\sum_{j=0}^{7}T^j L^{-1}\). Use the resulting matrix entries, including
their energy dependence and induced diagonal shifts, in the next
elimination. The even-sector active blocks reduce from 35 configurations
to 10 and then 3. The odd active block reduces from 20 to 6 and then 2.
The final central response uses a solve of size at most two and a scalar
root search. Both discarded blocks are strictly diagonally dominant at the
trial energies used by the generator.

The predictor lifts the central vector through both approximate
eliminations. It rounds the amplitudes to integers and then uses exact
rational residuals to bound the full energy from above and below. Lean
recomputes the residual using the direct pair-transfer rule. The lower
test covers every occupation, including the other blocked sectors. The
upper test uses the lifted trial vector supported on the active block.
This gives an end-to-end error bound for the composed reduction.
[Sparse certificate checker](Grain/ShellCertificate.lean) · [Prediction theorem](Grain/ShellPrediction.lean)

| Quantity | Value in spacing units |
| --- | --- |
| Mixed contrast from the reduced model | \(2.964666163\times10^{-8}\) |
| Lean-verified interval for the full contrast | \([2.964650171,\ 2.964680015]\times10^{-8}\) |
| Certified absolute error in the mixed contrast | \(\le 2\times10^{-13}\) |
| Certified absolute error per sector energy | \(\le 10^{-12}\) |

### Scalar matching through cubic order

The second-order hop cancellation gives \(g^2/(2r)\) in parity for a
shell at \(\pm r\). Bare central-orbital parity is \(g/2\). Matching
these energies gives a coupling shift of \(g^2/r\) per removed shell.
The four-case mixed contrast cancels this additive correction.

Within each reference block the pair count is fixed, so the diagonal
pairing shift cancels from every excitation gap. Let \(D\) be the
diagonal matrix of kinetic gaps above the reference, \(v\) its vector
of hop indicators, and \(T\) the adjacency matrix of hops between excited
occupations. The ground-energy shift \(\lambda\) relative to the
reference diagonal satisfies the scalar Schur equation
\[
\lambda=-g^2v^\mathsf{T}(D-gT-\lambda I)^{-1}v.
\]
At \(g=0\) all gaps are positive and the reference is the isolated
ground state. Hence \(\lambda=O(g^2)\), and the coefficient of \(g^3\)
is \(-v^\mathsf{T}D^{-1}TD^{-1}v\). It sums ordered three-hop loops
through the reference. Loops that avoid the central orbital are common
to all three sectors and cancel in parity.

For shell radii \(x_i\), a central hop has inverse gap
\(w_i=1/(2x_i)\), and a hop from the filled shell \(i\) to the empty
shell \(j\) has inverse gap \(p_{ij}=1/[2(x_i+x_j)]\). The surviving
loops in either even sector join two distinct central hops or join a
central hop and an ordinary hop sharing its other endpoint. The latter
contribute \(2\sum_{i,j}w_i p_{ij}=\sum_{i,j}w_iw_j\), by symmetry and
\((w_i+w_j)p_{ij}=w_iw_j\). The former contribute
\(\sum_{i\ne j}w_iw_j\). With the central orbital blocked in the odd
sector, their sum gives the cubic parity coefficient
\[
C_3=2\Bigl(\sum_i w_i\Bigr)^2-\sum_i w_i^2.
\]
For \(x=(d,r,s)\), the mixed difference of \(C_3\) is
\((1/r_{\rm near}-1/r_{\rm far})(1/s_{\rm near}-1/s_{\rm far})\).
The benchmark's leading cubic term is \(d/35{,}000{,}000\).
[Schur composition](Grain/Schur.lean#L128) · [Loop and mixed-coefficient proofs](Grain/ParityMatching.lean)

Let \(A=1/r+1/s\), \(Q=1/r^2+1/s^2\), and \(u=1/d\). The retained
three-orbital parity at coupling \(k\) through cubic order is
\(k/2+k^2u/2+k^3u^2/4\). The full parity has cubic coefficient
\((u+A)^2/2-(u^2+Q)/4\). Substituting \(k=g+g^2A+g^3B\) into the
retained parity gives cubic coefficient \(B/2+Au+u^2/4\). Equating
them fixes the scalar update used by the script
\[
g_{\mathrm{eff}}=g+g^2A+g^3\bigl(A^2-Q/2\bigr).
\]
The former reciprocal formula \(g/(1-gA)\) adds an extra \(g^3Q/4\)
to the parity at each spectrum through cubic order. This extra term
is additive in the two shells, so the former formula gives the same
leading **mixed** coefficient despite the error in each parity.
[Scalar matching and remainder](Grain/ParityMatching.lean)

The exact three-orbital solve at the cubic-matched coupling gives a
mixed contrast of about \(2.94439136\times10^{-8}d\). The first possible
difference from the full-model contrast is at fourth order. The
matrix-valued reduction encloses the full contrast through its residual check.
Run `--scalar-control` to reproduce the scalar interval.
[Scalar control](scripts/two_shell_prediction.py)

Lean bounds the resolvent remainder using the exact block eigenvector
equations. Let \(\Delta\) be a lower bound on the discarded kinetic gaps,
\(B\) a bound on the absolute row sums of \(T\), and \(V\) a bound on
\(\sum_i |v_i|\), with \(|v_i|\le 1\). For \(gB<\Delta\) and \(\lambda\le0\),
set \(U=1/\Delta\), \(W=BU/\Delta\), and \(Y=1/(\Delta-gB)\). The exact
discarded solution has maximum absolute entry at most \(Y\). Substituting
\(D^{-1}v+gD^{-1}TD^{-1}v\) into its equation leaves a residual from the
second tail hop and the energy shift. Bounding that residual and applying
the same discarded-block estimate gives the absolute sector-energy error
\[
g^4 VY\bigl[BW+VY(U+gW)\bigr].
\]
[Eigenvector normalization and resolvent remainder](Grain/ResolventRemainder.lean)

In spacing units the reference block has \(\Delta=2\). Each pair transfer
moves two electrons across at least one spacing. The seven-orbital blocks
have at most \(3\cdot4=12\) hops per row, and the three-orbital blocks
have at most two. The ground state lies in the reference block. Other
blocked configurations cost at least one spacing in kinetic energy, have
at most the reference pair count, and have absolute off-diagonal row sums
bounded by \(12g\) in the full model or \(2g_{\mathrm{eff}}\) in the scalar model.
These row bounds place their eigenvalues above the reference diagonal,
which itself bounds the ground energy from above. The benchmark
substitution gives sector error bounds of \(2.52\times10^{-6}d\) and
\(1.6\times10^{-8}d\), respectively. Including the polynomial matching
remainder gives a conservative analytic mixed-contrast error bound of
\(2.04\times10^{-5}d\). Lean also checks this budget directly against the
certified sector enclosures. The scalar checker reconstructs the three-orbital
Hamiltonians on all occupations and checks rational ground-energy witnesses.
Combining these with the frozen nested reduction bounds the signed difference
(full minus scalar) in \([2.025,\,2.030]\times10^{-10}d\). The independent
full solve sharpens this to \([2.027478,\,2.027483]\times10^{-10}d\).
[Benchmark budget](Grain/ScalarError.lean) · [Certified scalar comparison](Grain/ScalarCertificate.lean)

The prediction data and hashes record the four cases and the interval
frozen before the full solve. The provenance audit uses the archived
predictor source for that freeze.
[Prediction data](artifacts/two_shell_prediction.json) · [Frozen hashes](artifacts/two_shell_prediction.sha256.json) · [Archived predictor](artifacts/two_shell_original/two_shell_prediction.py)

## Independent solve in the frozen level-spacing regime

All consecutive one-particle spacings in the four chosen spectra are at
least \(d=100g\). The full assembler uses the frozen bare inputs and
enumerates all ternary occupations at fixed particle number. Each occupied
pair contributes \(-g\) to the diagonal. Every allowed transfer from a
paired orbital to an empty orbital contributes \(-g\) to the corresponding
off-diagonal entry in the matrix. The independent calculation includes
every blocked configuration.

| Electrons | Dimension in each spectrum | Undirected pair transfers |
| --- | ---: | ---: |
| 6 | 357 | 945 |
| 7 | 393 | 1071 |
| 8 | 357 | 945 |

The solver finds connected components from the full sparse matrix. It uses
exact fraction-free bisection on the shifted blocks to bracket the ground
energy and constructs rational test vectors from a shifted solve. Lean
checks the lower and upper bounds against the original occupation
Hamiltonians. The full-solve certificates import the shared occupation
model and checker. The comparison with the frozen reduction lives in
the validation module. [Independent certificates](Grain/ShellFullData.lean) · [Validation](Grain/ShellValidation.lean)

The certified mixed contrast is
\([2.9646661616,\ 2.9646661624]\times 10^{-8}d\). This enclosure is inside
the frozen prediction window, and the discrepancy from the frozen center
is at most \(1.4\times10^{-17}d\).

The [sparse matrix archive](artifacts/two_shell_full_solve.json) stores the
basis and off-diagonal pattern once per sector. Decode each edge with
`divmod(edge, dimension)` to obtain its zero-based row and column. Insert
the common off-diagonal value in both orientations and use the case's
`diagonal_scaled` for the diagonal. Divide the entries by `matrix_scale`
to recover the Hamiltonian in units of \(d\). An occupation code is ternary
with the lowest orbital in the least significant digit.

## Virtual phonons generate the same pairing

Keep the four frozen orbital spectra and put two spin modes on each orbital.
Use 21 independent bond oscillators and seven local density oscillators,
all at energy \(\Omega=5\times10^{13}d\). The electronic Hamiltonian contains
the one-particle energies \(K\). The bare electron–phonon term is linear in
each oscillator coordinate and in its one-body electronic vertex \(A_j\).

\[
H=K+\Omega\sum_j a_j^\dagger a_j+
\Omega\alpha\sum_j(a_j+a_j^\dagger)A_j,
\qquad \alpha=10^{-8}.
\]

A bond vertex is the sum of both spin-conserving one-electron hops across
its bond. A density vertex is the corresponding orbital occupation
operator. The microscopic Hamiltonian starts with zero direct
electron–electron interaction. The frequency is deliberately
antiadiabatic so the elimination error can be resolved against the
small frozen parity signal. This is a synthetic model of the virtual
phonon mechanism. [Bardeen and Pines](https://doi.org/10.1103/PhysRev.99.1140)
· [Bardeen, Cooper and Schrieffer](https://doi.org/10.1103/PhysRev.106.162)

In the vacuum and one-quantum compression, the exact Schur complement keeps
the electronic resolvent \((K+(\Omega-z)I)^{-1}\) between the two vertices.
The energy estimate below uses the full harmonic form.
[One-quantum response proof](Grain/PhononBridge.lean)

Completing the harmonic square gives an electronic comparison operator
\(K-\Omega\alpha^2\sum_j A_j^2\) plus positive squares. The local bond table
in Lean includes both virtual spin paths and their fermionic signs. On
a pair–empty bond, the two paths give a pair transfer with coefficient
\(-2\Omega\alpha^2=-g\). For separated orbitals the extra sign from
intervening occupations is identical on both legs and squares to one.
The sum of the bond return amplitudes is 24 on the low blocks of
\(N=6,7,8\). The site return contribution is \(N+2p\), where \(p\) is the
number of occupied pairs. The resulting block equals the reduced BCS
block plus the energy offset \(-g(12+N/2)\). The offset cancels in each
parity energy. [Local exchange proof](Grain/PhononExchange.lean)
· [Coupling and offset proof](Grain/PhononBridge.lean)

Lean constructs the fixed-number spinful basis and composes the signed
one-electron hops. It checks the sparse active rows against the shifted
reduced BCS action, including the two spin copies in the odd sector.
For the remaining blocks it checks that the kinetic energy minus the
uniform vertex-norm allowance lies above the electronic upper endpoints.
[Spinful vertices](Grain/Spinful.lean) · [Electronic comparison](Grain/PhononElectronic.lean)

For the microscopic upper bound, take an electronic trial vector \(x\)
from the full reduced-BCS certificate. Put \(x\) in the phonon vacuum
and \(-\alpha A_jx\) in the state with one quantum in mode \(j\). Its
expectation includes the actual electronic kinetic energy of the
one-quantum components. The lower bound holds for every finite-support
harmonic state, since the remaining terms are positive squares. The
trial uses only zero and one quanta. It bounds the unrestricted
finite-support variational infimum without an assumption on the tail.
The variational estimate uses \(K\le80d\,I\) and
\(\sum_j\lVert A_jx\rVert^2\le112\) for unit \(x\). The latter follows
from at most two unit-amplitude hops in any row of a symmetric bond
vertex, and density eigenvalues at most two. These bounds yield a
sector allowance of \(2\times10^{-12}d\).
Lean defines the microscopic ground energies as Rayleigh infima over
finite-support states in the oscillator occupation basis and proves all
twelve inequalities
\[
E_N^{\mathrm{BCS}}-g(12+N/2)\ \le\ E_N^{\mathrm{phonon}}\ \le\
E_N^{\mathrm{BCS}}-g(12+N/2)+2\times10^{-12}d.
\]
The bounds imply a positive microscopic mixed contrast and a difference
from the reduced BCS mixed contrast of at most \(8\times10^{-12}d\).
[Harmonic Hamiltonian](Grain/PhononHamiltonian.lean) · [Microscopic ground-energy theorem](Grain/PhononGround.lean)

The Python calculation evaluates the dressed trial with exact rational
arithmetic and gives the tighter microscopic contrast enclosure
\[
[2.964657750981,\ 2.9646745730575]\times10^{-8}d.
\]
This lies inside the original frozen prediction window.
[Microscopic energy record](artifacts/phonon_bridge.json)
· [Spinful checker](scripts/phonon_bridge.py)

## Which couplings dominate in MgB2?

Removing intraband σ attraction causes the largest drop in the leading
static phonon pairing eigenvalue. In the four-sheet calculation, the
eigenvalue falls from about 1.019 to 0.386. Removing intraband π attraction
or removing the two interband terms together leaves it at about 1.005 or
0.966, respectively. The two-band ordering holds throughout a range that
includes both independent electronic-structure calculations.
[Lean theorems](Grain/MgB2.lean)

The material input is the zero-transfer moment of the phonon kernel. Each
time-reversed transition contributes \(2|g_\nu|^2/\Omega_\nu\), or
\(|A_\nu|^2/\Omega_\nu^2\) in the mass-weighted derivative convention
used above. Liu, Mazin and Kortus tabulate the Fermi-surface averages
\(U_{ij}\) of this moment for four sheets, along with the partial densities
of states \(N_i\). Their data give the dimensionless gap matrix \(U_{ij}N_j\).
Lean bounds the leading eigenvalue using the symmetric kernel
\(N_i U_{ij}N_j\) with diagonal metric \(N_i\). The two-band calculation
assumes a constant trial gap on each group and averages the interaction
with both densities of states. The resulting leading eigenvalue differs
from the full four-sheet value by less than 0.003 before any channel is
removed. The independent Brinkman calculation supplies its own two-band
moment matrix. [Liu et al., Tables I and II](https://arxiv.org/pdf/cond-mat/0103570) ·
[Brinkman et al., page 2](https://arxiv.org/pdf/cond-mat/0111115) ·
[Retained inputs](artifacts/mgb2_pairing_inputs.json)

| Static input | All channels | Omit σ–σ | Omit π–π | Omit σ–π and π–σ |
|---|---:|---:|---:|---:|
| Liu, four sheets | 1.0189 | 0.3857 | 1.0051 | 0.9659 |
| Liu, grouped to two bands | 1.0159 | 0.3856 | 1.0017 | 0.9638 |
| Brinkman, two bands | 1.0701 | 0.5124 | 1.0485 | 1.0170 |

Each removal sets only the named entries to zero and leaves the other
couplings and densities of states fixed. Lean proves that removing σ–σ
still causes the largest drop, exceeding 0.18, if every entry of either
two-band input varies independently by up to 0.10 and the couplings stay
nonnegative. The 0.10 allowance is a sensitivity test on the static
couplings. The calculation supplies no estimate of the error from
electronic structure or Brillouin-zone sampling.
[Rational eigenvalue certificates](Grain/MgB2Data.lean)

The independently computed mode table from Shukla and collaborators
identifies the in-plane boron bond-stretching \(E_{2g}\) doublet. At the
A point it contributes 5.66 out of 6.06 to the sum of the nine calculated
mode couplings, more than 93%. The calculated 2.83 per component lies
inside the interval \([2.8,4.4]\) from their inelastic X-ray measurements
and calculated density of states. A separate integration by Kong and
collaborators traces the leading bulk spectral peak to σ holes coupled
to bond-stretching phonons near Γ–A. The 93% figure applies at A. The
band ablations concern the Brillouin-zone-averaged, static phonon
attraction and leave Coulomb repulsion, retardation and the bulk transition
temperature outside the certificate.
[Shukla et al., Tables I and II](https://arxiv.org/pdf/cond-mat/0209064) ·
[Kong et al., spectral analysis](https://arxiv.org/pdf/cond-mat/0102499)

```sh
python3 -B scripts/mgb2_pairing.py
python3 -B scripts/mgb2_pairing.py --lean > /tmp/MgB2Data.lean
diff -u Grain/MgB2Data.lean /tmp/MgB2Data.lean
lake build Grain.MgB2
lake env leanchecker Grain.PairingAttribution Grain.MgB2Data Grain.MgB2
```

## Electronic structure to pairing eigenvalue

[`scripts/pairing.py`](scripts/pairing.py) computes the largest eigenvalue
of a finite, anisotropic linearized Migdal–Eliashberg pairing equation.
It uses real time-reversed pair scattering, even-frequency gaps, and
static screened Coulomb matrix elements on the retained frequency grid.
The phonon interaction retains its transfer-frequency dependence and also
determines the normal-state mass renormalization.
[Anisotropic Migdal–Eliashberg equations](https://arxiv.org/abs/1211.3345)

The input JSON specifies the projection of electronic-structure and
screening calculations onto Fermi-surface patches. See the synthetic
[two-patch input](artifacts/pairing_example.json) for the format.

- `patch_weights_per_mev` contains positive **per-spin** DOS weights
  \(w_i\) in states per meV per cell, including the Fermi-surface
  quadrature weights. Their sum is the projected DOS. Band and momentum
  labels are implicit in the patch indices.
- Each `transitions` entry names one unordered zero-based patch pair
  in `patches`, a screened pair-scattering element `coulomb_mev`, and
  a list of phonon contributions in `modes`. Each mode gives its
  positive `energy_mev` and squared vertex `vertex_sq_mev2`. If a
  transition represents several sampled phonon contributions, include
  their averaging weights in the squared vertices. Use the same cell
  normalization for the DOS and interaction data.
- Omitted pairs have zero attraction and repulsion.
  The validator rejects duplicated patch pairs, nonpositive phonon
  energies, and negative squared vertices or Coulomb elements.
  Integers, decimals, and strings such as `"1/500"` are read exactly.

With \(\tau=\pi k_B T\) and \(\omega_n=(2n+1)\tau\), the phonon
contribution for a transfer \(\nu\) is
\[
P_{ij}(\nu)=\sum_\alpha
  \frac{2\Omega_{ij\alpha}|g_{ij\alpha}|^2}{\Omega_{ij\alpha}^2+\nu^2}.
\]
Folding the negative Matsubara frequencies into the positive ones gives
\[
F_{in,jm}=P_{ij}(\omega_n-\omega_m)+P_{ij}(\omega_n+\omega_m)-2C_{ij},
\quad
Z_{in}=1+\frac{1}{2n+1}\sum_{jm} w_j
[P_{ij}(\omega_n-\omega_m)-P_{ij}(\omega_n+\omega_m)].
\]
With \(x_{in}=w_i\Delta_{in}/(2n+1)\) and
\(D_{in,in}=(2n+1)Z_{in}/w_i\), the gap equation is \(Fx=\lambda Dx\).
The diagonal metric is positive and the kernel is symmetric. The
threshold is \(\lambda_{\max}=1\). The solver handles mixed signs in
the kernel by bisecting on positive definiteness of \(uD-F\).
A rational Rayleigh trial gives the lower bound and a rational LDLᵀ
factor gives the upper bound. [Lean assembly and certificate soundness](Grain/Pairing.lean)

From this directory, evaluate at individual temperatures or search a
range using \(\tau\) in meV. The reported Kelvin values are approximate
unit conversions.

```sh
python3 -B scripts/pairing.py artifacts/pairing_example.json --positive-frequencies 2 --at 4 8
python3 -B scripts/pairing.py artifacts/pairing_example.json --positive-frequencies 2 \
  --bracket 4 8 --temperature-tolerance 1/32
```

The example brackets a crossing in \([175/32,11/2]\) meV in \(\tau\),
about \([20.20065,20.31608]\) K. The fixed-size finite kernel is
continuous in positive temperature, so strict opposite endpoint signs
give a crossing without a monotonicity assumption. If eigenvalue bounds
overlap one at intermediate temperatures, the search may return a wider
bracket and reports whether it met the requested tolerance.

Append `--lean` to emit a certificate for the evaluated points or the
final bracket. Lean constructs the kernel from the supplied patch and
mode data and checks both eigenvalue witnesses. The
[example certificate](Grain/PairingExample.lean) is generated by the
second command with `--lean` and built with the project.
The certificate covers exact arithmetic on the specified finite input.
Electronic-structure accuracy, the Fermi-surface projection, frequency
truncation, and the validity of Migdal–Eliashberg theory for a material
require separate error estimates. A bracket establishes at least one
crossing in the specified range. The example uses synthetic parameters
and a two-frequency grid to keep the certificate small.

### Band mesh and Matsubara frequency error bounds

[`scripts/pairing_material.py`](scripts/pairing_material.py) accepts
finite band samples and uncertain phonon and Coulomb data. Use the
[example input](artifacts/pairing_material_example.json) as the export
format for an electronic-structure calculation.

- For each patch, give the band energies relative to the chemical
  potential as `xi_mev` and the normalized per-spin k-point weights as
  `quadrature_weight`. A band sample contributes its weight divided
  by twice the `fermi_halfwidth_mev` when its energy lies in the closed
  Fermi window. When its energy interval intersects both the window
  and its exterior, the contribution ranges from zero to that value.
  Lean bounds the DOS from these inclusion tests. Every patch must
  have a strictly positive lower DOS bound.
- Give the same unordered pair transitions as above. Each phonon
  energy, squared vertex and screened Coulomb element accepts a
  scalar or an interval `[lo, hi]`. The transitions refer to the
  declared patches, so any averaging weights on the phonon vertices
  belong in the supplied squared-vertex values.
- The Coulomb cutoff is the fixed number of positive frequencies
  on which the repulsion acts, on both indices of the pairing
  matrix. It stays fixed throughout the temperature scan. The
  normal-state sum includes every checked frequency and uses the
  retarded phonon interaction.

Lean encloses the phonon exchange and the diagonal normal-state
renormalization for every real realization of those inputs. The solver
diagonalizes only the retained frequency block. For the lower bound,
the trial vector has zero amplitude on the discarded frequencies, and
its Rayleigh numerator is bounded directly with the interval endpoints
appropriate to each product of amplitudes. For the upper bound, the
reference kernel has zeros outside the retained block. The absolute
error of its matrix entries gives a diagonal allowance through
\(2|x_i x_j|\le x_i^2+x_j^2\). The checked upper pencil therefore has a
retained block and a diagonal complement. This accounts for both the
input intervals and the omitted interactions in the larger checked grid.
[Input enclosures](Grain/PairingMaterial.lean)
· [Spectral certificate](Grain/PairingRobust.lean)

```sh
python3 -B scripts/pairing_material.py artifacts/pairing_material_example.json \
  --retained-frequencies 2 --checked-frequencies 3 --coulomb-frequencies 2 \
  --bracket 3 12 --temperature-tolerance 1/64
```

The synthetic example encloses a crossing for each admissible realization
between \(33/8\) and \(213/32\) meV in \(\pi k_B T\), approximately
15.24–24.59 K. The solver reports that this interval exceeds the requested
temperature tolerance. It preserves the certified signs when uncertainty
prevents further refinement. With `--lean`, the certificate proves a
crossing by continuity and produces a nonzero solution of the pairing
equation for each symmetric realization. [Continuity and eigenvector proofs](Grain/PairingCrossing.lean)
· [Example certificate](Grain/PairingMaterialExample.lean)

### Harmonic parent and the all-frequency crossing

For the finite real, spin-degenerate parent, let \(K_\alpha\) be the
mass-weighted force eigenvalue and \(d_{ij\alpha}\) the parent
deformation matrix element. At bosonic transfer \(\nu\), the quadratic
Fourier action has stiffness \(K_\alpha+\nu^2\). Completing its square
and translating the Gaussian integral gives the mixed Cooper term
\(-d_{ij\alpha}^2/(K_\alpha+\nu^2)\). Lean checks that its magnitude
equals \(P_{ij\alpha}(\nu)\) with \(\Omega_\alpha=\sqrt{K_\alpha}\) and
\(g_{ij\alpha}=d_{ij\alpha}/\sqrt{2\Omega_\alpha}\). The screened
interaction on orbital pairs is the matrix element of the parent's
screened operator between the corresponding two-electron occupation
states. The parent input supplies the screening convention.
[Harmonic elimination and Cooper projection](Grain/PairingParent.lean)

The mass renormalization uses the one-phonon normal self-energy
with a constant DOS in each patch and its electronic energy integral
extended to the real line. In that approximation, the energy integral of
the normal propagator gives \(-i\pi w_j\operatorname{sgn}(\omega_m)\).
For a symmetric flat band of half-width \(W\), Lean evaluates the
positive-frequency radial factor as \(2\arctan(W/\omega)\) and
bounds its difference from \(\pi\) by \(2\omega/W\).
The positive and negative internal frequencies therefore contribute with
opposite signs. For \(p_{ij}(k)=P_{ij}(2\tau k)\), Lean telescopes the
folded sum to the exact all-frequency metric
\[
D_{in}=\frac{2n+1+\sum_j w_j\left[p_{ij}(0)+2\sum_{k=1}^{n}p_{ij}(k)\right]}{w_i}.
\]
A finite normal-state sum on \(0\le m<N\) misses only the explicitly
bounded terms from \(N-n\) through \(N+n\). The pairing kernel still
has infinitely many rows. If \(A_{ij}=\sum_\alpha
2\Omega_{ij\alpha}|g_{ij\alpha}|^2/(4\tau^2)\), then
\(p_{ij}(k)\le A_{ij}/k^2\) for \(k\ge1\). For a retained row \(n<N\),
its coupling to omitted columns is at most
\[
\sum_j\left[\frac{2A_{ij}}{N-n}+\frac{2A_{ij}}{N+n+1}\right].
\]
Each omitted row has sum bounded by
\(\sum_j[p_{ij}(0)+4A_{ij}]\), while its bare metric is at least
\((2N+1)/w_i\). These bounds apply when the fixed Coulomb support fits
within the checked grid. Together they give an \(O(1/N)\) spectral
error bound uniform on any temperature interval bounded away from zero.
Lean proves continuity of the all-frequency variational spectral top
from this uniform convergence.
[Normal sum and row bounds](Grain/PairingFrequency.lean) ·
[Spectral convergence](Grain/PairingFull.lean)

Run the all-frequency certificate on the same synthetic inputs.

```sh
python3 -B scripts/pairing_material.py artifacts/pairing_material_example.json \
  --retained-frequencies 2 --checked-frequencies 3 --coulomb-frequencies 2 \
  --all-frequencies --bracket 3 12 --temperature-tolerance 1/64
lake build Grain.PairingFullExample
lake env leanchecker Grain.PairingFrequency Grain.PairingFull \
  Grain.PairingFrequencyCertificate Grain.PairingFullExample
```

At \(\tau=3\) meV the certified spectral top is at least 1.0849695,
and at \(\tau=12\) meV it is at most 0.9760019. This brackets an
all-frequency crossing for every symmetric realization in the input
intervals. Append `--lean` to reproduce the certificate. The wider
interval reflects the tail and row-sum allowances at the chosen grid size.
[Generated all-frequency certificate](Grain/PairingFullExample.lean)

A band calculation can interpret each supplied energy interval as an
enclosure over an entire quadrature cell. The cell DOS is then bounded
using its mass and its possible intersection with the Fermi window. Cells
wholly within the window contribute their full mass, and only cells
whose status is unresolved contribute quadrature uncertainty. Lean can
feed these integrated DOS values into the same pairing certificate.
[Cellwise band-mesh proof](Grain/PairingBandMesh.lean)

A material claim requires certified cell masses and band-energy
enclosures, projected phonon and screening data, and a parent-derived
bound on the vertex, material-specific bandwidth, patch projection,
and screening corrections to the normal and pairing response. Lean checks how
interaction row errors and normal-state diagonal errors consume the
endpoint margins of a finite pencil. The synthetic input supplies no
many-body residual or thermodynamic-limit result identifying the
spectral crossing with a bulk phase transition.
[Threshold error transfer](Grain/PairingProjection.lean) ·
[Anisotropic Eliashberg formalism](https://arxiv.org/abs/1211.3345)

## A periodic site model to BCS predictions

[`scripts/crystal_bcs.py`](scripts/crystal_bcs.py) starts from an
[explicit finite site model](artifacts/crystal_bcs_example.json). The
displacement array gives a real, periodic one-body hopping Hamiltonian
on \((\mathbb Z/2)^d\), with the entries indexed in binary order. The
other inputs are a site stiffness \(K>0\), the linear deformation
potential \(\gamma\), a screened on-site repulsion \(U\), and the
chemical potential \(\mu\). All sites share these parameters. No
band energies or pairing strength are supplied.

For site occupations \(n_\uparrow,n_\downarrow\), the structural
energy is \(Kq^2/2+\gamma q(n_\uparrow+n_\downarrow)+U n_\uparrow n_\downarrow\).
Minimizing over the real displacement \(q\) gives a one-body shift
\(-\gamma^2/(2K)\) and a pair term with coefficient
\(U-\gamma^2/K\). Lean proves this identity and checks that the real
periodic orbitals diagonalize the resulting normal Hamiltonian and resolve
the identity. Lean checks the exact matrix elements of the on-site
interaction between time-reversed pairs. For the four-site example the
attraction in this constant Cooper matrix is \(3/8\) meV. Keeping just
these matrix elements defines the Cooper-only Hamiltonian. Its accuracy
for the uniform pair response depends on the [omitted-channel error](#which-terms-the-cooper-projection-omits).
[Static reduction, band check, and pair projection](Grain/CrystalBCS.lean)

Write \(B=\sum_i c_{i\downarrow}c_{i\uparrow}\) in the band basis. For any
real trial field \(\Delta\) and attraction \(G>0\), the exact identity is
\[
 -GB^\dagger B
 = -\Delta(B+B^\dagger)+\frac{\Delta^2}{G}I
   -G\left(B-\frac{\Delta}{G}I\right)^\dagger
      \left(B-\frac{\Delta}{G}I\right).
\]
Keeping the first two terms defines the quadratic approximation.
The empty/doubly occupied block on level \(i\) has eigenvalues
\(\xi_i\pm E_i\), with \(\xi_i=\varepsilon_i-\mu\) and
\(E_i=\sqrt{\xi_i^2+\Delta^2}\). The two singly occupied states each
have energy \(\xi_i\). Tracing these four states and adding the field
cost gives the quadratic free-energy functional at \(t=k_BT>0\),
\[
 \mathcal F_t(\Delta)=\frac{\Delta^2}{G}
  +\sum_i\left[\xi_i-E_i-2t\log(1+e^{-E_i/t})\right].
\]
At zero temperature the level contribution is \(\xi_i-E_i\).
Lean differentiates the functional and obtains
\[
 \mathcal F_t'(\Delta)=\frac{2\Delta}{G}\bigl(1-R_t(\Delta)\bigr),
 \qquad R_t(\Delta)=G\sum_i\frac{\tanh(E_i/2t)}{2E_i}.
\]
For \(\Delta>0\), the strict decrease of \(R_t\) makes the gap equation
\(R_t(\Delta)=1\) equivalent to global minimization over nonnegative
amplitudes. This derives self-consistency from the quadratic free energy.
[Operator identity](Grain/CooperThermal.lean) · [Variational derivation](Grain/BCSVariational.lean)

The zero-temperature numerator is one. Lean proves that \(R_t(0)\)
is the leading real pairing eigenvalue for the attractive constant
channel, proves uniqueness of its crossing of one, and checks the
existence and uniqueness of nonzero gap amplitudes from their certified
brackets. For the attractive channel, it proves that a positive thermal
gap exists exactly below the critical temperature. The solver checks endpoint signs using
rational exponential and square-root enclosures.
[Gap response](Grain/BCS.lean) · [Positive-temperature proof](Grain/BCSThermal.lean)
· [Enclosure soundness](Grain/BCSCertificate.lean)
· [BCS theory](https://journals.aps.org/pr/abstract/10.1103/PhysRev.108.1175)

```sh
python3 -B scripts/crystal_bcs.py artifacts/crystal_bcs_example.json --at 1/5 1/2
python3 -B scripts/crystal_bcs.py artifacts/crystal_bcs_example.json --at 1/5 1/2 --lean
```

The quadratic free energy loses its positive minimizing amplitude at
\(T_c^{\rm MF}\) between approximately 3.5376565 and 3.5376638 K. The same
calculation gives a zero-temperature pair potential of about 0.567674 meV,
and a minimum zero-temperature quasiparticle excitation of about
0.581273 meV. The finite-temperature example is paired at
\(k_BT=1/5\) meV and above its pairing threshold at \(k_BT=1/2\) meV.
The root bracket measures numerical uncertainty within the gap equation.
The JSON output gives the exact rational intervals in energy units. The Lean certificate
rebuilds the bands, Cooper matrix and response inequalities from the site
inputs and the rational witnesses.
[Root certificates](Grain/CrystalBCSExample.lean) · [Certified minima](Grain/CooperBenchmark.lean)

At zero source the exact finite Cooper Gibbs state has
\(\langle B
angle=0\) by number gauge symmetry and
\(\langle B^\dagger B
angle>0\) for a nonzero pair operator.
The exact four-site free energy is analytic at all positive temperatures,
including throughout the mean-field threshold interval. A bulk critical
temperature requires a thermodynamic limit. The finite grain instead
has a directly calculable pair response to an applied source.
[Finite Gibbs state](Grain/CooperThermal.lean) · [Four-site analyticity](Grain/CooperBenchmark.lean)

The gap and threshold calculations use a finite, static model with fixed
chemical potential and sampled levels separated from it. The hopping,
stiffness, deformation potential and screened repulsion are effective
inputs. Applying the calculation to a metal specified by nuclear charges
and geometry requires a validated calculation of those inputs, control
of the static and BCS approximations, and a bulk limit. The retarded
solver above has its own finite Matsubara grid.

## Four-site thermal response across the reductions

The four-site crystal also defines a quantum Holstein–Hubbard model. Each
site has an independent oscillator at the specified energy `--phonon`,
the same deformation potential and stiffness as in the crystal input, and
the same on-site screened repulsion. The oscillator zero-point energy is
omitted since it cancels from the response.

For \(B=\sum_a c_{a\downarrow}c_{a\uparrow}\), add the source
\(-\eta(B+B^\dagger)\) at the same chemical potential in every calculation.
The observable is \([F_T(0)-F_T(h)]/(2h^2)\), the finite-source curvature per
site. A number gauge rotation makes \(F_T(h)=F_T(-h)\). The command reports
an interval for the response and for the signed discrepancy at each reduction.

- The oscillator displacement generates the on-site shift and attraction.
  It also transforms the hopping and pair source. The vacuum block carries
  the resulting displacement overlap factors. The trace bound includes both
  the vacuum-to-excited block coupling and all excited phonon occupations.
  In the displaced basis, write \(H=\Omega N_{\rm ph}+V\), with
  \(\|V\|\le v\). If \(b\) bounds the coupling from the vacuum block to its
  complement, quadratic-form order bounds the full Hamiltonian below by
  \(H_{\rm vac}-\delta\) and \(\Omega N_{\rm ph}-v-b^2/\delta\) on the
  two respective blocks. The trace of the latter bound sums the four
  oscillator ladders through a geometric series. The vacuum trace also
  supplies a lower bound on the full partition function.
- The full Hubbard calculation uses the instantaneous coefficients and all
  256 electronic Fock states. The exact Cooper calculation retains the
  projected interaction \(-GB^\dagger B\), with \(G=3/8\) meV for the
  example. Both traces use rational matrix-exponential enclosures.
- At each source the BCS calculation minimizes the free energy of the
  quadratic Hamiltonian over the real pair field after dropping the
  fluctuation square from \(-GB^\dagger B\). Its finite-source response uses the same free-energy
  difference as the electronic models. At a fixed quasiparticle energy,
  the negative logarithm uses the upper Boltzmann-factor bound for the
  lower free-energy endpoint and the lower bound for the upper endpoint.

```sh
python3 -B scripts/four_site_eft.py artifacts/crystal_bcs_example.json
```

The retained [four-site calculation](artifacts/four_site_eft.json) uses
\(h=0.05\) meV, \(k_BT=0.2,0.5\) meV, and \(\Omega=32,512\) meV. At
\(k_BT=0.2\) meV the Hubbard, exact Cooper, and mean-field responses are
about 1.7532, 5.7207, and 27.9581 per site per meV. At \(\Omega=512\) meV
the thermal enclosure bounds the absolute parent–Hubbard discrepancy by
0.03 per site per meV at both temperatures. The \(\Omega=32\) meV enclosure
is much wider. The chosen frequencies are
synthetic control parameters.

### How much the discarded square changes the source response

Let \(D(\eta)=F_{\rm MF}(\eta)-F_{\rm Cooper}(\eta)\), with the pair
field minimized separately at each source. Restoring the negative square
lowers the free energy at each source. The signed response error depends
on how much of that lowering survives subtraction,
\[
 \chi_{\rm MF}-\chi_{\rm Cooper}=\frac{D(0)-D(h)}{2h^2}.
\]
At \(k_BT=0.2\) meV the costs are about 0.907050 meV at zero source and
0.795863 meV at \(h=0.05\) meV. Subtracting the free-energy enclosures
gives \(0.11118692 < D(0)-D(h) < 0.11118693\) meV. This accounts for
the excess response of 22.2374 per site per meV. The four-site JSON reports
these signed intervals for both temperatures. Lean proves the interval
propagation in `pairing_response_error` conditional on the input bounds.
[Free-energy enclosures](artifacts/four_site_eft.json) · [Response error propagation](Grain/EFTBounds.lean)

The Lean comparison uses the certified zero-source minimizing amplitude
as a trial total field at the nonzero source. It bounds the mean-field
response from below without solving the sourced gap equation. At
\(k_BT=0.2\) meV it proves the response excess is greater than 19 per
site per meV, or equivalently \(D(0)-D(h)>0.095\) meV. The exact
Cooper response lies in \([5.720669,5.720670]\) at \(0.2\) meV and
\([1.942374,1.942375]\) at \(0.5\) meV.
[Four-site error certificate](Grain/CooperBenchmark.lean)

For an error bound without the full Cooper trace, use
\(Q_\eta=B-(\Delta_\eta/G)I\) at each source, where \(\Delta_\eta\)
is the internal pair field. The finite Gibbs variational inequalities
give both endpoints
\[
 G\langle Q_\eta^\dagger Q_\eta\rangle_{{\rm MF},\eta}
 \;\le\;D(\eta)\;\le\;
 G\langle Q_\eta^\dagger Q_\eta\rangle_{{\rm Cooper},\eta}.
\]
The lower endpoint is the mean-field variance times \(G\) when the
field is self-consistent. A quadratic-form bound
\(\|Q_\eta v\|^2\le c_\eta\|v\|^2\) supplies the upper endpoint
\(G c_\eta\) without a parent trace. Lean proves both bounds.
If \([\ell_\eta,u_\eta]\) encloses the cost at each of the two sources,
the signed response error lies in
\([(\ell_0-u_h)/(2h^2),(u_0-\ell_h)/(2h^2)]\). This interval gives a
test of the mean-field approximation at a specified temperature and
source.
[Fluctuation bounds](Grain/CooperFluctuation.lean) · [Response error propagation](Grain/EFTBounds.lean)

### Which terms the Cooper projection omits

In the four-site momentum basis, the Hubbard interaction is
\(-G\sum_q B_q^\dagger B_q\), where momentum addition is XOR and
\(B_q=\sum_k c_{q\oplus k,\downarrow}c_{k,\uparrow}\).
The uniform source probes \(B_0+B_0^\dagger\). This operator preserves
total momentum, and each \(B_q^\dagger B_q\) also preserves it because the
incoming and outgoing pairs have the same momentum. The \(q\ne 0\) terms can
therefore act inside the same many-body momentum sectors as the source,
change their Gibbs weights, and change their response. The Cooper model
keeps the 16 terms with \(q=0\). The other terms consist of 12 diagonal
opposite-spin density terms, 12 spin-exchange terms, and 24 scattering
terms with four distinct momenta. The last group connects complementary
sets of singly occupied momenta. The other groups preserve those sets.

Write \(H_{\rm Hub}(\eta)=H_{\rm Cooper}(\eta)+W\), with
\(W=-G\sum_{q\ne0}B_q^\dagger B_q\), and define
\(D(\eta)=F_{\rm Hub}(\eta)-F_{\rm Cooper}(\eta)\) at the same temperature
and chemical potential. The signed error from restoring the omitted channels is
\[
  \chi_{\rm Hub}-\chi_{\rm Cooper}=\frac{D(0)-D(h)}{2h^2}.
\]
Bounds on \(D\) at the two sources give a signed interval for this error.
A sufficient bound that needs only the omitted interaction is obtained
from \(\ell I\le W\le u I\). By the min–max principle, every ordered
eigenvalue shifts by an amount in \([\ell,u]\) at each source. Lean
propagates these spectral bounds through the Boltzmann sum and logarithm
to obtain \(D(\eta)\in[\ell,u]\) and hence
\[
  |\chi_{\rm Hub}-\chi_{\rm Cooper}|\le\frac{u-\ell}{2h^2}.
\]
One can use \(u=0\) for the attractive sum of pair squares and bound
\(-\ell\) by the maximum absolute row sum of \(W\) in the Fock basis.
The channel selection is controlled at a given \(t,h\) if the resulting
error bound meets the observable's tolerance. For example, an absolute
error bound \(\delta\) gives \(\chi_{\rm Hub}\ge\chi_{\rm Cooper}-\delta\).
Thus \(101\delta\le\chi_{\rm Cooper}\) suffices for 1% relative accuracy
using only the reduced response and the error bound. The spectral estimate
can be loose for small \(h\), so the four-site calculations use
source-specific trace bounds.
[Response error proofs](Grain/EFTBounds.lean)

The table rounds the response per site per meV. Applicability means an
absolute discrepancy of at most **1% of the full Hubbard response**,
at the benchmark's fixed chemical potential and source \(h=0.05\) meV.

| Terms retained alongside Cooper | \(k_BT=0.2\) meV | \(k_BT=0.5\) meV |
| --- | --- | --- |
| None | 5.72067, inapplicable | 1.94237, inapplicable |
| Density | 1.76164, applicable | 1.24164, inapplicable |
| Spin exchange | 5.66628, inapplicable | 1.87421, inapplicable |
| Four distinct momenta | 5.09792, inapplicable | 1.75090, inapplicable |
| Density + spin exchange | 1.75974, applicable | 1.22151, inapplicable |
| Density + four distinct momenta | 1.76107, applicable | 1.21269, inapplicable |
| Spin exchange + four distinct momenta | 4.74015, inapplicable | 1.64415, inapplicable |
| All three (full Hubbard) | 1.75321, reference | 1.17263, reference |

Lean bounds the Cooper-only excess over Hubbard by \([3.967455,3.967457]\)
at \(k_BT=0.2\) meV and \([0.769742,0.769744]\) at \(k_BT=0.5\) meV,
in the same response units. Both exceed the 1% error budget.
The labels apply to these two temperatures for this sample and observable.
Other temperatures, source strengths, chemical potentials, lattices, and
observables are unassessed. Density gives the largest suppression in
every tested combination. In a configuration with \(p\) doubly occupied
momenta and no singles it contributes exactly \(-Gp(p-1)\).
Density and exchange together retain the spin-invariant combination. At zero source and
\(k_BT=0.2\) meV, the filled-state Gibbs weight is approximately 0.0162%
for Cooper, 95.82% after restoring density, and 95.08% for full Hubbard.
The four-state pair-removal block has a certified uniform-source resolvent
coefficient of \(11936/6609\) in the same response units.

Lean checks the Fourier coefficients, the signed matrix data, coverage of
all 256 Fock states, the rational Taylor traces and their remainder bounds,
and the inequalities defining applicability. Python proposes the witnesses. The separate check script builds certificates
serially under a 14 GiB per-process address-space limit. A fresh run checks
large exact-integer witnesses and can take tens of minutes. The ordinary
project build excludes this benchmark.
[Channel operators](Grain/HubbardOperators.lean) ·
[Thermal trace certificate](Grain/HubbardTrace.lean) ·
[Applicability theorems](Grain/HubbardBenchmark.lean)

```sh
python3 -B scripts/hubbard_channels.py --check
bash scripts/check_hubbard_lean.sh
```

### Prediction at a withheld temperature

The uniform source preserves total crystal momentum \(K\) (the XOR of
occupied momenta) and spin imbalance \(M=N_\uparrow-N_\downarrow\).
Each scattering term creates and destroys one electron of each spin, with
the same incoming and outgoing pair momentum \(q\). The source creates
or destroys both spins at the same momentum, so its net momentum is zero.
The kinetic term is diagonal in momentum. Thus the \(K=M=0\) block,
which contains the filled state and its pair-removal states, closes at
both source values. It contains 16 configurations with each momentum
empty or doubly occupied and six with four singles and two spins of
each kind. Scattering at four distinct momenta connects these two
families. All 16 Cooper, 12 density, 12 exchange and 24 four-momentum
monomials act in this 22-state block. The reduction uses these
conservation laws to restrict states while retaining every interaction
channel. [Sector and channel checks](Grain/HubbardOperators.lean)

The displaced phonon vacuum uses the same interaction in this block.
Each intersite hop changes the displacement of two oscillators and
has vacuum overlap \(e^{-a}\), where \(a=(\gamma^2/K_{\rm spring})/(2\Omega)\)
and \(K_{\rm spring}\) is the site stiffness. A pair source changes one
oscillator's displacement by twice the single-electron amount and has
overlap \(e^{-2a}\). The finite-source trace uses \(h e^{-2a}\) in the
Hamiltonian and the imposed \(2h^2\) in the normalization.

Let \(A\) be the retained block and \(D\) its complement. Write
\(w=Z_D(0)/Z_A(0)\), \(R=Z_A(h)/Z_A(0)\) and \(d=Z_D(h)/Z_D(0)\).
The signed error made by keeping only \(A\) is
\[
  \chi_{\rm full}-\chi_A
    = \frac{t}{2h^2}\log\!\left(\frac{1+w d/R}{1+w}\right).
\]
The predictor evaluates the retained traces and bounds the discarded
traces using the diagonal, row radii and lower bounds on the connected
blocks' ground energies from rational positive-definiteness tests.
For a discarded matrix \(H_D\), Jensen's inequality bounds the trace
below by \(\sum_i e^{-(H_D)_{ii}/t}\). The min–max principle bounds each
ordered eigenvalue below using the sorted diagonal-minus-row-radius
values and the ground energy bound. The discarded source satisfies
\(1\le d\le\cosh(h\|S_D\|/t)\), where \(S_D\) includes the overlap in the
vacuum calculation. Convexity and number gauge symmetry give the lower
bound. For the upper bound, apply Golden–Thompson at both source signs
and average so that the source factor is \(\cosh(h S_D/t)\). The
predictor intersects this bound on the partition ratio with the interval
from the two discarded trace bounds. The parent interval also includes
overlap rounding, virtual phonon mixing and excited phonon Gibbs weight.
The predictor uses all 234 discarded configurations for the tail bounds
and evaluates the Hubbard matrix-exponential trace on the retained block.
Lean checks the partition-ratio identity and endpoint propagation given
the trace bounds. Python evaluates the holdout enclosures.
[Interval proof](Grain/EFTBounds.lean)

The prediction was saved at \(k_BT=1/8\) meV with \(h=1/20\) meV
and \(\Omega=512\) meV before evaluating the full site-basis traces.
The zero-source discarded-to-retained partition ratio for instantaneous
Hubbard was bounded between 0.00207 and 0.00285. The validator independently
assembles the 256-state electronic matrices from site hopping and local
interactions. It also constructs the retained sector by averaging signed
site translations in the spin-balanced space, evaluates its traces there,
and checks the overlap factors from the changes in site occupation.
The validation artifact records the prediction's SHA-256 digest.

| Signed error, per site per meV | Predicted interval (rounded outward) | Site-basis check (approx.) |
| --- | ---: | ---: |
| Full Hubbard minus retained Hubbard | \([-0.004929,\ 0.048550]\) | \(-0.002080\) |
| Full phonon vacuum minus retained phonon vacuum | \([-0.004834,\ 0.047650]\) | \(-0.002039\) |
| Full Hubbard minus bare Cooper | \([-5.295667,\ -5.242187]\) | \(-5.292817\) |
| Quantum parent minus retained phonon vacuum | \([-0.024213,\ 0.070303]\) | Analytic phonon bound |

The prediction gives a conservative relative error bound of 2.71%.
The observed Hubbard discrepancy is about 0.116%, within the 1% benchmark
criterion above. The predicted signed error interval for bare Cooper
already places it outside the 1% budget at this temperature.

Here the retained dressed matrix uses the lower rational endpoints of
the overlaps. The discarded-to-retained partition ratio for the vacuum
in the JSON refers to that rational matrix. The full vacuum response
interval includes overlap rounding. The parent bound uses the infinite
oscillator tail estimate above and places the parent response between
1.7590 and 1.8536 per site per meV. The bare Cooper response is about
7.09035 in the same units.
The independent numerical check covers the electronic and vacuum traces.
[Saved prediction](artifacts/four_site_prediction.json) ·
[Independent validation](artifacts/four_site_validation.json)

The grain parity energy compares fixed-particle-number ground-state
energies at zero temperature. The four-site response measures the change
in grand-canonical free energy under a finite pair source at positive
temperature. The BCS instability gives the temperature at which the
zero-source normal mean-field solution loses linear stability.

```sh
python3 -B scripts/four_site_prediction.py predict artifacts/crystal_bcs_example.json
python3 -B scripts/four_site_prediction.py validate artifacts/crystal_bcs_example.json \
  artifacts/four_site_prediction.json
```

## Single-band harmonic model from a DFPT export

The harmonic-model importer takes one exact rational export in the case format
below. The orbitals are samples of one spin-degenerate band in a real basis.
The screened interaction uses the supplied density terms and ordered
two-creation, two-annihilation terms. No fit to a pairing strength enters the
reconstruction.

```sh
lake build Grain.HarmonicBandExample
python3 -B scripts/dfpt_harmonic.py artifacts/dfpt_harmonic_example.json > /tmp/DFPTHarmonic.lean
lake env lean /tmp/DFPTHarmonic.lean
```

For a shell experiment JSON, pass `--case NAME` to select its primitive export.
The generated module stores the band levels, screened terms, and phonon input.
Lean computes the Cartesian projection when supplied, constructs signed
Fock-space matrix elements, and checks positive squared frequencies,
polarization orthonormality, and screened interaction symmetry. Vertex
symmetry follows from the signed annihilation overlaps. In the
example, a Cartesian mode produces the orbital derivative
`[[2, 1], [1, -1]]`. The fixture also includes screened density and signed
pair-transfer terms.

For each mode with frequency `Ω` and mass-weighted derivative `A`, the
assembled parent uses the coupling `A / √(2Ω)`. Lean derives the
instantaneous electronic comparison by completing the oscillator squares,
including the full `-A²/(2Ω²)` contribution. It proves the corresponding
lower bound on the harmonic quadratic form for every oscillator occupation
box. The harmonic form represents the exact declared finite input and uses
the supplied screening convention.
The upstream sector-error field is carried as export metadata.
This stage provides the parent Hamiltonian and a one-sided form comparison.
Quantitative accuracy for pair response and the applicability of BCS require
further reductions and bounds.

Use `--pair-transfer` to resolve the off-diagonal matrix element between
two doubly occupied orbitals. The JSON report gives the screened electronic
entry, the sum of the phonon entries and the signed instantaneous transfer
in meV. Nonzero mode entries are sorted by magnitude and identified by
their zero-based export indices. Each entry is a signed overlap of the
one-hop states reached from the two paired determinants. For separate
eigenvectors of a degenerate doublet, the invariant contribution is their
sum within the degenerate subspace. The harmonic example gives
\(-1/3-1/4=-7/12\) meV. The sector error field bounds specified
ground-energy discrepancies and supplies no entrywise error in this report.

```sh
python3 -B scripts/dfpt_harmonic.py artifacts/dfpt_harmonic_example.json --pair-transfer
```

[Reconstruction and comparison proof](Grain/HarmonicBand.lean) ·
[Example Lean certificate](Grain/HarmonicBandExample.lean)

## Shell predictions from DFPT exports

The DFPT interface takes one export per physical configuration. All cases
use the same number-sector and contrast conventions, and each brings its own
one-particle energies, phonon vertices, and electronic interaction. In the
included synthetic fixtures the controlled intervention changes selected
orbital energies. For a real material, rerun the electronic and DFPT
calculation for each intervention and supply the resulting data.

Each case contains the following fields.

- `levels_mev` gives the real spin-degenerate orbital energies in ascending
  order. Orbital indices in other fields refer to this ordering.
- `mass_weighted_modes` gives positive `omega_squared_mev2` and sparse real
  upper-triangle `potential_derivative` entries `[i, j, value]` for each mode.
  The derivative is with respect to the mass-weighted coordinate, with
  \(\hbar=1\) and \(H_{\rm ep}=A_\nu(a_\nu+a_\nu^\dagger)/\sqrt{2\Omega_\nu}\).
  An export with `mass_weighted_cartesian_derivatives` can instead supply
  one sparse derivative list per Cartesian coordinate and an orthonormal
  `eigenvector` in each mode record. The predictor contracts those derivatives
  with the supplied DFPT mode vectors.
- `screened_density_terms` entries are
  `[orbital, spin, orbital, spin, coefficient_mev]`. More general real
  two-body terms in `screened_scattering_terms` are
  `[creation_slots, annihilation_slots, coefficient_mev]`. Each slot is
  `[orbital, spin]`. The written creation operators followed by the
  annihilation operators act in the stated product order, with the rightmost
  operator acting first. Supply both terms for a non-self-adjoint monomial.
  `screening_convention` records which polarization processes are included.
- `upstream_sector_error_mev` is an externally justified absolute bound
  per sector on discrepancies from the supplied harmonic model and orbital
  subspace. Zero means the declared finite model is the target. Material
  error budgets depend on the electronic-structure calculation.

The predictor assembles the full signed instantaneous interaction
\(-\sum_\nu A_\nu^2/(2\Omega_\nu^2)\) plus the supplied electronic
interaction. Kinetic filling determines the reference. The active space
retains orbitals nearest the Fermi rank and includes the ties. For \(L\)
orbitals, `odd_electrons` runs from \(1\) through \(2L-1\) in steps of two.
An empty or fully occupied neighboring sector retains its sole determinant.
The shell reduction works on the signed matrix as a whole. A certified positive
discarded pivot and a squared residual bound control the error in the Schur
complement, with the Jacobi order chosen from the requested resolution.
The printed second-order result comes from the assembled matrix. The
prediction interval uses the energy-dependent reduction. A dressed-trial
bound covers the difference from the harmonic parent over all oscillator
occupations. Its width determines whether the sign carries through.

```sh
python3 -B scripts/dfpt_shell_eft.py check artifacts/dfpt_5_orbital_example.json artifacts/dfpt_5_orbital_prediction.json
python3 -B scripts/dfpt_shell_eft.py validate artifacts/dfpt_5_orbital_example.json artifacts/dfpt_5_orbital_prediction.json
python3 -B scripts/dfpt_shell_eft.py check artifacts/dfpt_7_orbital_example.json artifacts/dfpt_7_orbital_prediction.json
python3 -B scripts/dfpt_shell_eft.py validate artifacts/dfpt_7_orbital_example.json artifacts/dfpt_7_orbital_prediction.json
```

For a new input, `predict INPUT` prints the prediction and `freeze INPUT
NEW_FILE` records it with hashes of the input and predictor. `validate` starts
from the same parsed primitive data. It projects any Cartesian derivatives,
assembles the screened and mode matrices on ordered determinants, and forms
the induced interaction from the Gram matrix of each mode. It then bisects
the full instantaneous electronic blocks using fraction-free tests. The
harmonic-parent enclosure is variational. Completing the oscillator squares
gives a lower bound from the electronic solve that applies to all phonon
occupations. A vacuum-plus-one-quantum dressed trial gives the upper bound.
The validation checks overlap for each sector and reports whether each
contrast enclosure lies inside the corresponding frozen interval.

The five-orbital fixture recovers the historical second-order center of
\(1/9000\) in coupling units. The seven-orbital mixed contrast vanishes at
second order and has a positive harmonic-parent enclosure
\([2.9645204,2.9648357]\times10^{-8}\) meV after elimination. The
[five-orbital validation](artifacts/dfpt_5_orbital_validation.json) and
[seven-orbital validation](artifacts/dfpt_7_orbital_validation.json) each
land inside the corresponding frozen instantaneous and parent intervals.

Lean certifies the five-orbital shell prediction directly. It assembles
signed Fock columns from the orbital energies, screened terms, and
mass-weighted derivatives. It checks the retained occupations and the
entries and closure of each component used in the reduction. Row bounds
cover the other determinants. [Five-orbital prediction](Grain/DFPTFivePrediction.lean)

At each trial energy the predictor supplies an approximate lift \(W\).
Lean checks the discarded-block lower bound \(\delta>0\) and computes
\(R=B^T+(D-zI)W\) from the checked blocks. The squared Frobenius norm
of \(R\) divided by \(\delta\) bounds the loss in the retained
quadratic form. Lean uses the corrected retained LDLᵀ factor or a lifted
trial vector to justify each bracket update. It checks the final width
and dresses the upper trial by using the existing vacuum and one-quantum
bound. A shell with an insufficient discarded gap or an unresolved
residual at the requested resolution can leave the prediction inconclusive.

The standalone prediction generator takes the export and frozen prediction.
Its Lean theorems enclose both the instantaneous and harmonic contrasts.
The second-order diagnostic is computed in Python. The certificates concern
the declared finite harmonic model. A material interpretation of a nonzero
upstream error requires an external justification of that budget.

The independent five-orbital full solve has its own Lean enclosures and
containment checks. The seven-orbital fixture also has full-solve certificates
for comparison with its recorded prediction. The full-solve certificates use
sparse row bounds, positive Gram factors, and rational trial vectors.
[Five-orbital validation](Grain/DFPTFive.lean) · [Seven-orbital validation](Grain/DFPTSevenContrast.lean)

```sh
python3 -B scripts/dfpt_shell_certificate.py artifacts/dfpt_5_orbital_example.json \
  artifacts/dfpt_5_orbital_prediction.json > /tmp/DFPTFivePrediction.lean
diff -u Grain/DFPTFivePrediction.lean /tmp/DFPTFivePrediction.lean
bash scripts/check_dfpt_lean.sh --prediction-only
```

After checking the prediction, reproduce and check the independent enclosure.

```sh
python3 -B scripts/dfpt_shell_eft.py validate artifacts/dfpt_5_orbital_example.json \
  artifacts/dfpt_5_orbital_prediction.json > /tmp/dfpt_5_orbital_validation.json
diff -u artifacts/dfpt_5_orbital_validation.json /tmp/dfpt_5_orbital_validation.json
python3 -B scripts/dfpt_certificate.py artifacts/dfpt_5_orbital_example.json \
  artifacts/dfpt_5_orbital_prediction.json /tmp/dfpt_5_orbital_validation.json \
  --namespace DFPTFive --shell-prediction > /tmp/DFPTFive.lean
diff -u Grain/DFPTFive.lean /tmp/DFPTFive.lean
bash scripts/check_dfpt_lean.sh
```

The DFPT runner builds the five-orbital prediction before the validation
module and checks the seven-orbital spectra in separate processes. It
sets a 14 GiB address-space limit per process. Use `--case-index` to
generate one seven-orbital spectrum's certificate and `--split` to
generate the module that combines them.

## Reproduce

From this directory with the pinned Lean toolchain and Python 3:

```sh
lake exe cache get Mathlib/Tactic.lean Mathlib/Basic/Real/Basic.lean Mathlib/Analysis/SpecialFunctions/Log/Basic.lean
bash scripts/check_dfpt_lean.sh
bash scripts/check_hubbard_lean.sh
lake build
lake env leanchecker Grain.Main
lake env leanchecker Grain.ParityMatching
lake env leanchecker Grain.ResolventRemainder Grain.ScalarError Grain.ScalarCertificate
lake env leanchecker Grain.ShellValidation
lake env leanchecker Grain.PhononBridge
lake env leanchecker Grain.PhononGround
lake env leanchecker Grain.Pairing Grain.PairingExample
lake env leanchecker Grain.PairingMaterial Grain.PairingRobust Grain.PairingCrossing Grain.PairingMaterialExample
lake env leanchecker Grain.PairingAttribution Grain.MgB2Data Grain.MgB2
lake env leanchecker Grain.BCS Grain.BCSCertificate Grain.BCSThermal Grain.CrystalBCS Grain.CrystalBCSExample
lake env leanchecker Grain.BCSVariational Grain.CooperThermal Grain.CooperFluctuation
lake env leanchecker Grain.EFTBounds
lake build Grain.Audit
python3 -B scripts/provenance.py verify
python3 -B scripts/certify.py --check
python3 -B scripts/two_shell_prediction.py --check
python3 -B scripts/two_shell_prediction.py --scalar-control
python3 -B scripts/two_shell_full_solve.py --check
python3 -B scripts/phonon_bridge.py --check
python3 -B scripts/test_eft_regressions.py
```

The Python checks reproduce the retained numerical artifacts byte for byte.
The Lean build checks the inequalities in the Lean certificates using kernel
reduction. Lean can verify those certificates directly.
