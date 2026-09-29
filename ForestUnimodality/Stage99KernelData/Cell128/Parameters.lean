import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 127
  A := (496112101443899260910797/3125000000000000000000000)
  B := (95061669071129201169512157/1000000000000000000000000000)
  C := (18078978598454412130003277/25000000000000000000000000)
  dδ := (12345208002978131922589/80000000000000000000000)
  dM := (16690285279228878317220319/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(15164888797071526482795889/2000000000000000000000000), (9061846084971398873619819/2500000000000000000000000), (30938838456510044494507383/1000000000000000000000000), (17182887257989289508941511/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11791/22366)
  hi := (23607/44732)
  vmin := (498697875/2000951824)
  damping := (498697875/2000951824)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell128
