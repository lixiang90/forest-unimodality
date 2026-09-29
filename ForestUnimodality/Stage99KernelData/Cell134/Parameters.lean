import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 123
  A := (11406753245769569616641093/100000000000000000000000000)
  B := (47642832657651089378614273/500000000000000000000000000)
  C := (34919644253294068736437339/50000000000000000000000000)
  dδ := (1880926339654972329062943/12500000000000000000000000)
  dM := (2063431557408827005627161/1250000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(69672755082546178329039321/10000000000000000000000000), (39917860773583178080059497/10000000000000000000000000), (13302541981489103051217171/500000000000000000000000), (615715893764093080697819/31250000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (95449/180624)
  hi := (47737/90312)
  vmin := (2032402775/8156257344)
  damping := (2032402775/8156257344)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell134
