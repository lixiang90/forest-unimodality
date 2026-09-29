import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell184
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 68
  A := (-294694670487087296595341/156250000000000000000000)
  B := (3356650505544105100863561/25000000000000000000000000)
  C := (59640272000624459936002353/10000000000000000000000000000)
  dδ := (15156265103494931389960243/200000000000000000000000000)
  dM := (432512126744503749235099/250000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(15549399653378051411323213/1000000000000000000000000), (6311843394648397165269671/125000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7977/15052)
  hi := (95749/180624)
  vmin := (8126696375/32625029376)
  damping := (8126696375/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell184
