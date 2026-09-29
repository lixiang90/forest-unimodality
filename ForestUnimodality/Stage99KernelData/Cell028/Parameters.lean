import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 91
  A := (86595368056962236270379663/100000000000000000000000000)
  B := (44882011914460992474396051/1000000000000000000000000000)
  C := (-50465164417738472835139873/100000000000000000000000000)
  dδ := (2304091781296199736850383/20000000000000000000000000)
  dM := (93563976264220323226378229/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(47845923888312835714486937/10000000000000000000000000), (4134384720901900234224513/1250000000000000000000000), (6871457005523116379208659/200000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (17/37)
  hi := (1613/3478)
  vmin := (340/1369)
  damping := (340/1369)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell028
