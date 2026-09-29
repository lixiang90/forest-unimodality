import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell436
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (26)
  A := (366571397070823732533551 / 3125000000000000000000000)
  B := (3090390931712197475356163 / 200000000000000000000000000)
  C := (-13338225191671455177599981 / 500000000000000000000000000)
  dδ := (14861245693106392082305511 / 1000000000000000000000000000)
  dM := (11565719586350401196749027 / 125000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(7934122833179015898963371 / 10000000000000000000000000), (40259598058240486651015999 / 10000000000000000000000000), (35103713158125162685507803 / 10000000000000000000000000)]
  retention := ![(3 / 5), (2 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13 / 42)
  hi := (20 / 63)
  vmin := (377 / 1764)
  damping := (3770000000000000000000000000000000000000000 / 43524955408804071509263948678105342569819369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell436
