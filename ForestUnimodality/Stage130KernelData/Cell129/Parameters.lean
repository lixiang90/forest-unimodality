import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 69
  A := (-9559994566366055385131517/5000000000000000000000000)
  B := (13475208688993567385239203/100000000000000000000000000)
  C := (9936569065530212463421833/2000000000000000000000000000)
  dδ := (74438028728849497950292857/1000000000000000000000000000)
  dM := (8642530707599644507199699/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1539464931329420949168707/100000000000000000000000), (5162389202923648667820089/100000000000000000000000)]
  retention := ![(3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (111/211)
  hi := (23557/44732)
  vmin := (498819475/2000951824)
  damping := (498819475/2000951824)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell129
