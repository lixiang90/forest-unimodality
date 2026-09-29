import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 42
  A := (7910718183070323589234363/5000000000000000000000000)
  B := (-5694419513379810060538233/2500000000000000000000000000)
  C := (-6946862915605132773183561/5000000000000000000000000000)
  dδ := (10320388209087634490135343/100000000000000000000000000)
  dM := (11936529769968106176603051/20000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(62069239915198224366577051/10000000000000000000000000), (22976317089742572363775253/1000000000000000000000000), (1787137255730489648897219/125000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4777/9702)
  hi := (3193/6468)
  vmin := (23526725/94128804)
  damping := (23526725/94128804)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell073
