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
synthetic harmonic electron–phonon Hamiltonian. Material calibration and
the thermodynamic phase remain separate scales.

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

As a scalar control, update \(g^{-1}\) by subtracting \(1/s\) and
\(1/r\), then solve the three-orbital model at that coupling. A separate
exact rational calculation on that small model gives a contrast of about
\(2.98595379\times10^{-8}d\), around 0.7% above the matrix-valued prediction.
The scalar control uses this particular update rule and budget. Its
numerical interval is reproducible with `--scalar-control`.

The [prediction data](artifacts/two_shell_prediction.json) and
[hashes](artifacts/two_shell_prediction.sha256.json) record the four cases and the interval frozen before the full solve. The
ground-energy bounds in this prediction come from the lifted residuals of
the reduced model.

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

### Band mesh and frequency truncation with error bounds

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

The error bound stops at `--checked-frequencies`. The Fermi-window
calculation is exact for the supplied finite samples. A prediction for
a bulk metal also requires independently justified band, phonon and
screening intervals, convergence of the band mesh and Fermi-window
projection, and a bound on the remaining frequency tail.
[First-principles EPW workflow](https://www.nature.com/articles/s41524-023-01107-3)

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
the identity. It projects the on-site pair interaction onto these orbitals
and verifies the resulting constant Cooper matrix. For the four-site
example the attraction in this matrix is \(3/8\) meV.
[Static reduction, band check, and pair projection](Grain/CrystalBCS.lean)

For the constant channel the finite-band BCS gap is a scalar \(\Delta\).
With normal energies \(\xi_i=\varepsilon_i-\mu\) and temperature in
energy units \(t=k_BT\), the BdG quasiparticle energy is
\(E_i=\sqrt{\xi_i^2+\Delta^2}\). The opposite-energy Fermi weights give
\(\tanh(E_i/2t)\), and the off-diagonal thermal pair amplitude gives the
scalar response
\[
R_t(\Delta)=G\sum_i\frac{\tanh(E_i/2t)}{2E_i}.
\]
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

The checked example gives \(T_c\) between approximately 3.5376565 and
3.5376638 K, a zero-temperature pair potential of about 0.567674 meV,
and a minimum zero-temperature quasiparticle excitation of about
0.581273 meV. The finite-temperature example is paired at
\(k_BT=1/5\) meV and above its pairing threshold at \(k_BT=1/2\) meV.
The JSON output gives the exact rational intervals. The Lean certificate
rebuilds the bands, Cooper matrix and response inequalities from the site
inputs and the rational witnesses.
[Example certificate](Grain/CrystalBCSExample.lean)

These are mean-field predictions for a finite, static model with fixed
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
- The BCS free energy minimizes the quadratic pair-field expression. Its
  pair coupling and constant term follow by completing the square in
  \(-GB^\dagger B\). Its finite-source response uses the same free-energy
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

### Which terms the Cooper projection omits

In the four-site momentum basis, the Hubbard interaction is
\(-G\sum_q B_q^\dagger B_q\), where momentum addition is XOR and
\(B_q=\sum_k c_{q\oplus k,\downarrow}c_{k,\uparrow}\).
The uniform source couples to \(B_0+B_0^\dagger\). The Cooper model
keeps the 16 terms with \(q=0\). The other terms consist of 12 diagonal
opposite-spin density terms, 12 spin-exchange terms, and 24 scattering
terms with four distinct momenta. The last group connects complementary
sets of singly occupied momenta. The other groups preserve those sets.

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

[DFPTFive.lean](Grain/DFPTFive.lean) and [DFPTSevenContrast.lean](Grain/DFPTSevenContrast.lean)
check the parameters and instantiate both sector bounds on the actual
exports. Lean builds the sparse signed Fock columns from the orbital
energies, screened terms, and mass-weighted derivatives. It checks the
instantaneous lower bounds across every fixed-number determinant and
the upper bounds with rational trial vectors. A mode-dependent row
allowance covers high kinetic energies. The lower-bound checker also
accepts exact positive factors for signed components where absolute
row bounds lose cancellations. For the harmonic model it
checks rational lower bounds on the mode frequencies and the cost of
dressing each trial. The lower comparison applies to every oscillator
occupation box, and the upper trial uses the vacuum and one quantum in
each mode. Lean propagates the signed parity contrast and proves that
both validation intervals, including the positive harmonic contrast,
lie inside the recorded prediction intervals.

The certificate generator takes the export and both recorded JSON files.
Python supplies candidate witnesses. The Lean proofs establish the output
enclosures by checking those witnesses against the parent operators.
The shell search and second-order diagnostics remain Python calculations.
The certificates concern the declared finite harmonic model. Any material
interpretation of a nonzero upstream error still depends on an external
justification of that budget.

```sh
python3 -B scripts/dfpt_certificate.py artifacts/dfpt_5_orbital_example.json \
  artifacts/dfpt_5_orbital_prediction.json artifacts/dfpt_5_orbital_validation.json \
  --namespace DFPTFive > /tmp/DFPTFive.lean
diff -u Grain/DFPTFive.lean /tmp/DFPTFive.lean
bash scripts/check_dfpt_lean.sh
```

The DFPT CI job builds and checks the seven-orbital spectra in separate
Lean processes. Its serial runner sets a 14 GiB address-space limit per
process. Use `--case-index` to generate one spectrum's certificate and
`--split` to generate the module that combines them.

## Reproduce

From this directory with the pinned Lean toolchain and Python 3:

```sh
lake exe cache get Mathlib/Tactic.lean Mathlib/Basic/Real/Basic.lean Mathlib/Analysis/SpecialFunctions/Log/Basic.lean
bash scripts/check_dfpt_lean.sh
lake build
lake env leanchecker Grain.Main
lake env leanchecker Grain.ShellValidation
lake env leanchecker Grain.PhononBridge
lake env leanchecker Grain.PhononGround
lake env leanchecker Grain.Pairing Grain.PairingExample
lake env leanchecker Grain.PairingMaterial Grain.PairingRobust Grain.PairingCrossing Grain.PairingMaterialExample
lake env leanchecker Grain.BCS Grain.BCSCertificate Grain.BCSThermal Grain.CrystalBCS Grain.CrystalBCSExample
lake env leanchecker Grain.EFTBounds
lake build Grain.Audit
python3 -B scripts/provenance.py verify
python3 -B scripts/certify.py --check
python3 -B scripts/two_shell_prediction.py --check
python3 -B scripts/two_shell_full_solve.py --check
python3 -B scripts/phonon_bridge.py --check
python3 -B scripts/test_eft_regressions.py
```

The Python checks reproduce the retained numerical artifacts byte for byte.
The Lean build checks the inequalities in the Lean certificates using kernel
reduction. Lean can verify those certificates directly.
