import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 22
  A := (19617173725909038296322251/100000000000000000000000000)
  B := (3053616079355624818303383/100000000000000000000000000)
  C := (-73633029455152571030041031/1000000000000000000000000000)
  dδ := (7144289896773522996475947/200000000000000000000000000)
  dM := (9489344585712376420327807/25000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(16642840366800195628371739/20000000000000000000000000), (34665583062645346501540189/5000000000000000000000000)]
  retention := ![(3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29/85)
  hi := (89/255)
  vmin := (1624/7225)
  damping := (2598400000000000000000000000000000000000000/28523156719148246408565263419438648532149201)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell012
