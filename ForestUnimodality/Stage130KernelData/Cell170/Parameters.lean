import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell170
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-4035994886713286491897179/2500000000000000000000000)
  B := (1117202975370099882201913/10000000000000000000000000)
  C := (3092142738292549364147177/625000000000000000000000000)
  dδ := (70343650119701214840084447/1000000000000000000000000000)
  dM := (13357753538211347005271179/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(17524078599160022307046347/2500000000000000000000000), (7772748486809692991528209/1250000000000000000000000), (6109238559446450267387263/100000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95599/180624)
  hi := (11953/22578)
  vmin := (127000625/509766084)
  damping := (127000625/509766084)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell170
