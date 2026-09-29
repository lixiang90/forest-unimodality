import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-18617640527284273110808499/10000000000000000000000000)
  B := (12178128932371530546152627/100000000000000000000000000)
  C := (6224052673528887710471813/1250000000000000000000000000)
  dδ := (34647853311770004935965517/500000000000000000000000000)
  dM := (7200725700424946392266823/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(305866148318375496995003/125000000000000000000000), (1347049858755334206250609/100000000000000000000000), (58156501708686491269872931/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
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
end ForestUnimodality.Stage130KernelData.Cell130
