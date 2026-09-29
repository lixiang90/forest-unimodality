import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 43
  A := (-10269919878547833057780281/100000000000000000000000000)
  B := (5016152143218523262735431/62500000000000000000000000)
  C := (7995049494144673696283121/2000000000000000000000000000)
  dδ := (11283539917280593911641517/100000000000000000000000000)
  dM := (4231228256362150005366607/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7101986035900154980993193/1000000000000000000000000), (356864868908886379017531/10000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22331/43056)
  hi := (27/52)
  vmin := (675/2704)
  damping := (675/2704)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell110
