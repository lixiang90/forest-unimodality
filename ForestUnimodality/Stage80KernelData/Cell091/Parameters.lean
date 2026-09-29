import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 40
  A := (-8502466809831952826215229/25000000000000000000000000)
  B := (406976144330883748967409/4000000000000000000000000)
  C := (9125687375957313406116267/5000000000000000000000000000)
  dδ := (6000245095663506861294323/50000000000000000000000000)
  dM := (10924736804827463784034469/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(9869540244787995408870529/2500000000000000000000000), (11566548462356374127324443/5000000000000000000000000), (16640302886391072689775683/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (51/101)
  hi := (10429/20604)
  vmin := (106115075/424524816)
  damping := (106115075/424524816)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell091
