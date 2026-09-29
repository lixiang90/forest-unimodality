import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 35
  A := (-16781433709858044721840997/100000000000000000000000000)
  B := (10213337799362701141525633/100000000000000000000000000)
  C := (74595472305242936303382173/10000000000000000000000000000)
  dδ := (6398123144672135387267531/50000000000000000000000000)
  dM := (24938812475106333921281987/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(26923776686843559069473031/5000000000000000000000000), (26553605138379041683549531/10000000000000000000000000), (26671576896018649449615623/1000000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
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
end ForestUnimodality.Stage80KernelData.Cell123
