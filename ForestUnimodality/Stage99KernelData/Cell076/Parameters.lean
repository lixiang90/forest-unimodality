import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 50
  A := (-91372469383787395912577267/100000000000000000000000000)
  B := (10466171961171177873239913/100000000000000000000000000)
  C := (1509376233072873776009/781250000000000000000000)
  dδ := (89860534675244393976178969/1000000000000000000000000000)
  dM := (16770416570604373008440691/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(10022793632136244301733541/5000000000000000000000000), (7971663147343781119502637/1000000000000000000000000), (39022134899294186993756739/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (26/51)
  hi := (3579/7004)
  vmin := (12258075/49056016)
  damping := (12258075/49056016)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell076
