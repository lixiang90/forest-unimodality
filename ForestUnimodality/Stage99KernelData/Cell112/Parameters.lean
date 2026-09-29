import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 50
  A := (-69425764357004020709496217/100000000000000000000000000)
  B := (94994443601193051529563149/1000000000000000000000000000)
  C := (9417876696767425379053229/2000000000000000000000000000)
  dδ := (18119934969788009659907857/200000000000000000000000000)
  dM := (1571844357790753814174689/1000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(288976186087823876391667/40000000000000000000000), (2099772848386690782263031/50000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2294/4389)
  hi := (1531/2926)
  vmin := (2135745/8561476)
  damping := (2135745/8561476)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell112
