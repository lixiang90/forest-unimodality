import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 68
  A := (-9318143687043821349291761/5000000000000000000000000)
  B := (6537543902694344100101631/50000000000000000000000000)
  C := (27395519170444926522478557/5000000000000000000000000000)
  dδ := (73541621267052909027839291/1000000000000000000000000000)
  dM := (16627391041271586021033091/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(15542497989988568463104457/1000000000000000000000000), (126314551887924242379313/2500000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31833/60208)
  hi := (23881/45156)
  vmin := (508068275/2039064336)
  damping := (508068275/2039064336)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell157
