import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 55
  A := (8913412582792204997161889/50000000000000000000000000)
  B := (10203804963655378756914871/200000000000000000000000000)
  C := (-6114662572565591168449739/1000000000000000000000000000)
  dδ := (44672619548428119107263967/500000000000000000000000000)
  dM := (11837667216260422831802801/12500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(8258220457938149072774081/5000000000000000000000000), (63185580668941119242276727/10000000000000000000000000), (9424969103329962649695517/200000000000000000000000)]
  retention := ![(4/5), (7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22/47)
  hi := (1677/3572)
  vmin := (550/2209)
  damping := (550/2209)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell030
