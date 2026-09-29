import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell195
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 65
  A := (-863985703489590434855927/3125000000000000000000000)
  B := (5688794718376146558602713/50000000000000000000000000)
  C := (48610147007477744196535241/100000000000000000000000000)
  dδ := (13044475485557421867710559/100000000000000000000000000)
  dM := (5605500781038117667082199/2500000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(15125859946411024381518473/2500000000000000000000000), (22602098916843115006258813/1000000000000000000000000)]
  retention := ![(7/10), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (6/11)
  hi := (97/177)
  vmin := (7760/31329)
  damping := (7760/31329)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell195
