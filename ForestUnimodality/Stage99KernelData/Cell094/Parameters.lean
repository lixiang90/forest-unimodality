import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 49
  A := (-12668530137024179321514339/25000000000000000000000000)
  B := (21844081192922824852242769/250000000000000000000000000)
  C := (19147569968673968862638013/5000000000000000000000000000)
  dδ := (46884456098515006616800349/500000000000000000000000000)
  dM := (3766626913027843782943993/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(36474891242235387700532101/5000000000000000000000000), (642317986685447706030061/15625000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7427/14352)
  hi := (11153/21528)
  vmin := (115712375/463454784)
  damping := (115712375/463454784)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell094
