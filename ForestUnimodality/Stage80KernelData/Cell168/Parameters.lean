import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 98
  A := (-15674031246998251287294579/50000000000000000000000000)
  B := (14966380891221031657067897/100000000000000000000000000)
  C := (19824968858644956282155647/25000000000000000000000000)
  dδ := (9848578521881024006034977/50000000000000000000000000)
  dM := (31583114535073393384922991/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(1280835513247618129284433/125000000000000000000000), (3435176604165865654749723/100000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (12116/22791)
  hi := (24257/45582)
  vmin := (517280525/2077718724)
  damping := (517280525/2077718724)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell168
