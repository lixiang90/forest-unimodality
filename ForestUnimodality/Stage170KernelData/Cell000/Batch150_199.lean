import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell000.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch150_199
import ForestUnimodality.BinomialMassData.Q9_35.Batch150_199

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167680137347119117797/50000000000000000000)
  centralHi := (67072054938847647119/20000000000000000000)
  directionLo := (336491341226356758667/100000000000000000000)
  directionHi := (84122835306589189667/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree150.table
  base := (-7960664213842674809394129552389227258321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-35336838370707040618556861280000000000000)
      constant := (619147253851104403755441804790443090966716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree150.table
  base := (-7960664424020128452663711349430804997011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2227301226170676537105541724400000000000000)
      constant := (40275456341374070074022700223389452775732305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (336491341226356758667/100000000000000000000)
  centralHi := (84122835306589189667/25000000000000000000)
  directionLo := (168809309279457388041/50000000000000000000)
  directionHi := (337618618558914776083/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree151.table
  base := (-793487296709948626101453553274384214769/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-35576533136287498901295657360000000000000)
      constant := (628114590276451475388941745699024631409240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree151.table
  base := (-7934873151891110062993597369160294825977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2242401996402245408918085877440000000000000)
      constant := (40856451331662198115409201697363727767635635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168809309279457388041/50000000000000000000)
  centralHi := (337618618558914776083/100000000000000000000)
  directionLo := (338742144521385951149/100000000000000000000)
  directionHi := (6774842890427719023/2000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree152.table
  base := (-3954096847200737066204716526792623253781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-35816227901867957184034453440000000000000)
      constant := (637145402497012955914028419465659013969752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree152.table
  base := (-1581638771373307459574533413816526810421/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2257502766633814280730630030480000000000000)
      constant := (41441546942762140402961521666186754657234275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338742144521385951149/100000000000000000000)
  centralHi := (6774842890427719023/2000000000000000000)
  directionLo := (339861956317951332193/100000000000000000000)
  directionHi := (169930978158975666097/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree153.table
  base := (-1576125286106087307792081762953788514657/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-36055922667448415466773249520000000000000)
      constant := (646239690373661652869175479290924229706860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree153.table
  base := (-1576125314672090312212790142599009844991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2272603536865383152543174183520000000000000)
      constant := (42030743166242456792757717715228212939886025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339861956317951332193/100000000000000000000)
  centralHi := (169930978158975666097/50000000000000000000)
  directionLo := (340978090541874248339/100000000000000000000)
  directionHi := (17048904527093712417/5000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree154.table
  base := (-7852171209628690777217908613935806823429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-36295617433028873749512045600000000000000)
      constant := (655397453769828297068181141984256772706284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree154.table
  base := (-3926085667595749602862939174689106825833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-326814901013850289193674048080000000000000)
      constant := (6089148570545368418324853497515762522191690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340978090541874248339/100000000000000000000)
  centralHi := (17048904527093712417/5000000000000000000)
  directionLo := (342090583189453091407/100000000000000000000)
  directionHi := (21380661449340818213/6250000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree155.table
  base := (-62582624521793721678352448116850241989/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-36535312198609332032250841680000000000000)
      constant := (664618692551400975060596913291574879005500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree155.table
  base := (-7822828175602804903798666748035077280327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2302805077328520896168262489600000000000000)
      constant := (43221437417342941264884938859731406066319885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342090583189453091407/100000000000000000000)
  centralHi := (21380661449340818213/6250000000000000000)
  directionLo := (171599734836783517757/50000000000000000000)
  directionHi := (68639893934713407103/20000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree156.table
  base := (-974074628781720605543063371009882328549/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-36775006964189790314989637760000000000000)
      constant := (673903406586632666815800169407683765486432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree156.table
  base := (-7792597127280446133208089504256658237941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2317905847560089767980806642640000000000000)
      constant := (43822935428810454820498796315745118731704455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171599734836783517757/50000000000000000000)
  centralHi := (68639893934713407103/20000000000000000000)
  directionLo := (344304784836829115753/100000000000000000000)
  directionHi := (172152392418414557877/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree157.table
  base := (-1940369534271046352093990783186831497507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-37014701729770248597728433840000000000000)
      constant := (683251595746055989423764103699010696039888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree157.table
  base := (-3880739111185339580231387760309016642873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2333006617791658639793350795680000000000000)
      constant := (44428534020344286809820932769520581844992230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344304784836829115753/100000000000000000000)
  centralHi := (172152392418414557877/50000000000000000000)
  directionLo := (345406562964360487373/100000000000000000000)
  directionHi := (172703281482180243687/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree158.table
  base := (-7729471417532123456370346266780037918001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-37254396495350706880467229920000000000000)
      constant := (692663259902404356666561029132879848327996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree158.table
  base := (-1932367873124012104805154768654704435721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2348107388023227511605894948720000000000000)
      constant := (45038233184196913846605164123070389652993420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345406562964360487373/100000000000000000000)
  centralHi := (172703281482180243687/50000000000000000000)
  directionLo := (346504837796199115579/100000000000000000000)
  directionHi := (17325241889809955779/5000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree159.table
  base := (-7696576902882306164452580063730429135831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-37494091260931165163206026000000000000000)
      constant := (702138398930538859839691250935078283456676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree159.table
  base := (-3848288484385247530017806028691584794223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2363208158254796383418439101760000000000000)
      constant := (45652032912745420348965762363069123450830730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346504837796199115579/100000000000000000000)
  centralHi := (17325241889809955779/5000000000000000000)
  directionLo := (173799821269677800873/50000000000000000000)
  directionHi := (347599642539355601747/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree160.table
  base := (-7662794623904543547986943008130253296671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-37733786026511623445944822080000000000000)
      constant := (711677012707380258881697655167478986813316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree160.table
  base := (-7662794681813566370742548009639576827799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2378308928486365255230983254800000000000000)
      constant := (46269933198488017231383203072038303677189245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173799821269677800873/50000000000000000000)
  centralHi := (347599642539355601747/100000000000000000000)
  directionLo := (34869100987952833329/10000000000000000000)
  directionHi := (348691009879528333291/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree161.table
  base := (-7628124610869587509026756868042138731187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-37973480792092081728683618160000000000000)
      constant := (721279101111845546184366954757831445075252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree161.table
  base := (-3814062330881907738657152568116067794323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-341915671245419161006218201120000000000000)
      constant := (6698847719148679853999161584255875254397390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34869100987952833329/10000000000000000000)
  centralHi := (348691009879528333291/100000000000000000000)
  directionLo := (21861185749530603127/6250000000000000000)
  directionHi := (349778971992489650033/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree162.table
  base := (-7592566893563966060224015179128909222909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-38213175557672540011422414240000000000000)
      constant := (730944664024788609697091175563484363108364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree162.table
  base := (-3796283469145735001244667295497790128243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2408510468949502998856071560880000000000000)
      constant := (47518035412134439821227625883638082837160930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21861185749530603127/6250000000000000000)
  centralHi := (349778971992489650033/100000000000000000000)
  directionLo := (87715890138788562139/25000000000000000000)
  directionHi := (350863560555154248557/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree163.table
  base := (-236128796915746781136683192934465891217/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-38452870323252998294161210320000000000000)
      constant := (740673701328944578240689740654388365924224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree163.table
  base := (-472257596288152436500676572731484864209/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2423611239181071870668615713920000000000000)
      constant := (48148237325611652046836606200084579332300720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87715890138788562139/25000000000000000000)
  centralHi := (350863560555154248557/100000000000000000000)
  directionLo := (35194480675634059651/10000000000000000000)
  directionHi := (351944806756340596511/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree164.table
  base := (-93984855786854661833518059094737879239/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-38692565088833456576900006400000000000000)
      constant := (750466212908877481298342062529683878643520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree164.table
  base := (-3759394248744859580985060234466445609093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2438712009412640742481159866960000000000000)
      constant := (48782539767423991453498692853559441651544430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35194480675634059651/10000000000000000000)
  centralHi := (351944806756340596511/100000000000000000000)
  directionLo := (353022741307235699839/100000000000000000000)
  directionHi := (551598033292555781/156250000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree165.table
  base := (-7480567806911498923502008012829011602181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-38932259854413914859638802480000000000000)
      constant := (760322198650930898820627160498683953591276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree165.table
  base := (-748056783726425458391511815282742818261/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2453812779644209614293704020000000000000000)
      constant := (49420942730629396749564650920757280095260550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353022741307235699839/100000000000000000000)
  centralHi := (551598033292555781/156250000000000000)
  directionLo := (177048697225786578337/50000000000000000000)
  directionHi := (14163895778062926267/4000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree166.table
  base := (-3720729780587076998494257453674307192617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-39171954619994373142377598560000000000000)
      constant := (770241658443181314526933183050605542459064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree166.table
  base := (-7441459587845297214766652720492101564337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2468913549875778486106248173040000000000000)
      constant := (50063446208389611203628875947927435116737435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177048697225786578337/50000000000000000000)
  centralHi := (14163895778062926267/4000000000000000000)
  directionLo := (177584397987767020393/50000000000000000000)
  directionHi := (355168795975534040787/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree167.table
  base := (-7401463753295040404184225608683240030359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-39411649385574831425116394640000000000000)
      constant := (780224592175393919469087089395267039878564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree167.table
  base := (-3700731888365155380655167046730018748501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2484014320107347357918792326080000000000000)
      constant := (50710050193967756207528893504294290813234510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177584397987767020393/50000000000000000000)
  centralHi := (355168795975534040787/100000000000000000000)
  directionLo := (356236975217379784461/100000000000000000000)
  directionHi := (178118487608689892231/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree168.table
  base := (-7360580410421176100242085564357361920611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-39651344151155289707855190720000000000000)
      constant := (790270999738980641826477097742570552317556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree168.table
  base := (-7360580431012455127524352085606359950789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-357016441476988032818762354160000000000000)
      constant := (7337250668675143940684292440779777401722385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356236975217379784461/100000000000000000000)
  centralHi := (178118487608689892231/50000000000000000000)
  directionLo := (357301961076825874197/100000000000000000000)
  directionHi := (178650980538412937099/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree169.table
  base := (-731880955929788035195090395583802781147/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-39891038916735747990593986800000000000000)
      constant := (800380881026960204531947971366647888754120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree169.table
  base := (-7318809577389684720145918839377005588717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2514215860570485101543880632160000000000000)
      constant := (52015559662123366505761719716520633630764335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel170
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357301961076825874197/100000000000000000000)
  centralHi := (178650980538412937099/50000000000000000000)
  directionLo := (358363782024164832181/100000000000000000000)
  directionHi := (179181891012082416091/50000000000000000000)

def endpointA : IntegerEndpointWitness 170 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree170.table
  base := (-7276151226278296348238276493089290495467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-40130733682316206273332782880000000000000)
      constant := (810554235933920034829789327427642838018132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 170 interval.damping) (curvature.centralUpper 170 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree170.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 170 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree170.table
  base := (-909518905271686268405944550816473389447/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2529316630802053973356424785200000000000000)
      constant := (52674465131713517771466143494799712156683880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 170 interval.damping) (curvature.centralUpper 170 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree170.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 170 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 170 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel171
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (358363782024164832181/100000000000000000000)
  centralHi := (179181891012082416091/50000000000000000000)
  directionLo := (179711233054573315527/50000000000000000000)
  directionHi := (71884493221829326211/20000000000000000000)

def endpointA : IntegerEndpointWitness 171 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree171.table
  base := (-144652108746649797236439045934877654649/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-40370428447896664556071578960000000000000)
      constant := (820791064355979869629130169443024469070200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 171 interval.damping) (curvature.centralUpper 171 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree171.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 171 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree171.table
  base := (-7232605451297309630057317296878915203131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2544417401033622845168968938240000000000000)
      constant := (53337471083142769017702445555392665775232905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 171 interval.damping) (curvature.centralUpper 171 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree171.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 171 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 171 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel172
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179711233054573315527/50000000000000000000)
  centralHi := (71884493221829326211/20000000000000000000)
  directionLo := (360478040969624378417/100000000000000000000)
  directionHi := (180239020484812189209/50000000000000000000)

def endpointA : IntegerEndpointWitness 172 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree172.table
  base := (-898521527257019831934004582356662092673/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-40610123213477122838810375040000000000000)
      constant := (831091366190756917878890076244586813034464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 172 interval.damping) (curvature.centralUpper 172 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree172.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 172 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree172.table
  base := (-898521528790579202728027896439723632749/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2559518171265191716981513091280000000000000)
      constant := (54004577510148065083424615591330141679811960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 172 interval.damping) (curvature.centralUpper 172 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree172.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 172 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 172 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel173
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360478040969624378417/100000000000000000000)
  centralHi := (180239020484812189209/50000000000000000000)
  directionLo := (22595658364998300629/6250000000000000000)
  directionHi := (72306106767994562013/20000000000000000000)

def endpointA : IntegerEndpointWitness 173 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree173.table
  base := (-1785712898419745877772287719625413292349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-40849817979057581121549171120000000000000)
      constant := (841455141337332456451466562635993387322416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 173 interval.damping) (curvature.centralUpper 173 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree173.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 173 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree173.table
  base := (-3571425802228411823451662541329589642353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2574618941496760588794057244320000000000000)
      constant := (54675784406555072395165666094820501075247030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 173 interval.damping) (curvature.centralUpper 173 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree173.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 173 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 173 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel174
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22595658364998300629/6250000000000000000)
  centralHi := (72306106767994562013/20000000000000000000)
  directionLo := (90644992889821711613/25000000000000000000)
  directionHi := (362579971559286846453/100000000000000000000)

def endpointA : IntegerEndpointWitness 174 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree174.table
  base := (-7096643589072648404781418032088359503137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-41089512744638039404287967200000000000000)
      constant := (851882389696219749442427136311646561987452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 174 interval.damping) (curvature.centralUpper 174 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree174.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 174 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree174.table
  base := (-7096643598540664194413344337013935074339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2589719711728329460606601397360000000000000)
      constant := (55351091766276328753091510345719585906786945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 174 interval.damping) (curvature.centralUpper 174 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree174.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 174 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 174 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel175
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90644992889821711613/25000000000000000000)
  centralHi := (362579971559286846453/100000000000000000000)
  directionLo := (181813190289683597349/50000000000000000000)
  directionHi := (363626380579367194699/100000000000000000000)

def endpointA : IntegerEndpointWitness 175 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree175.table
  base := (-7049548228758554399432846187221894886273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-41329207510218497687026763280000000000000)
      constant := (862373111169333192600235765001112420454908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 175 interval.damping) (curvature.centralUpper 175 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree175.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 175 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree175.table
  base := (-7049548237075664585624581081939661417343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-372117211708556904631306507200000000000000)
      constant := (8004357083329922053355846401132111850392995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 175 interval.damping) (curvature.centralUpper 175 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree175.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 175 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 175 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel176
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181813190289683597349/50000000000000000000)
  centralHi := (363626380579367194699/100000000000000000000)
  directionLo := (364669786972499717969/100000000000000000000)
  directionHi := (36466978697249971797/10000000000000000000)

def endpointA : IntegerEndpointWitness 176 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree176.table
  base := (-1400313107383049845572228487545433937401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-41568902275798955969765559360000000000000)
      constant := (872927305659958594993621620329091321251980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 176 interval.damping) (curvature.centralUpper 176 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree176.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 176 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree176.table
  base := (-3500782772110563024575824964248187431433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2619921252191467204231689703440000000000000)
      constant := (56714007851735420455353328901726388158597830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 176 interval.damping) (curvature.centralUpper 176 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree176.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 176 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 176 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel177
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (364669786972499717969/100000000000000000000)
  centralHi := (36466978697249971797/10000000000000000000)
  directionLo := (14628408657561401791/4000000000000000000)
  directionHi := (45713777054879380597/12500000000000000000)

def endpointA : IntegerEndpointWitness 177 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree177.table
  base := (-6952695537385592251063907577609181632731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-41808597041379414252504355440000000000000)
      constant := (883544973072724519178594299119563273469076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 177 interval.damping) (curvature.centralUpper 177 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree177.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 177 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree177.table
  base := (-6952695543802987754132203159623103692063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2635022022423036076044233856480000000000000)
      constant := (57401616565716871902239997817804339595444565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 177 interval.damping) (curvature.centralUpper 177 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree177.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 177 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 177 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel178
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14628408657561401791/4000000000000000000)
  centralHi := (45713777054879380597/12500000000000000000)
  directionLo := (366747694314774651987/100000000000000000000)
  directionHi := (91686923578693662997/25000000000000000000)

def endpointA : IntegerEndpointWitness 178 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree178.table
  base := (-6902938253683672458887063595324017193467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-42048291806959872535243151520000000000000)
      constant := (894226113313574609195770113418703931226132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 178 interval.damping) (curvature.centralUpper 178 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree178.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 178 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree178.table
  base := (-6902938259320464243368753560772526414777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2650122792654604947856778009520000000000000)
      constant := (58093325719496501151164315923722731028379635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 178 interval.damping) (curvature.centralUpper 178 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree178.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 178 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 178 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel179
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366747694314774651987/100000000000000000000)
  centralHi := (91686923578693662997/25000000000000000000)
  directionLo := (367782245578169426779/100000000000000000000)
  directionHi := (18389112278908471339/5000000000000000000)

def endpointA : IntegerEndpointWitness 179 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree179.table
  base := (-6852293709001495401361466409085593668689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-42287986572540330817981947600000000000000)
      constant := (904970726289740842845025639553657625325244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 179 interval.damping) (curvature.centralUpper 179 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree179.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 179 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree179.table
  base := (-3426146856976242776942278358729133708547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2665223562886173819669322162560000000000000)
      constant := (58789135307395470343055585601030724482811970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 179 interval.damping) (curvature.centralUpper 179 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree179.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 179 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 179 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel180
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367782245578169426779/100000000000000000000)
  centralHi := (18389112278908471339/5000000000000000000)
  directionLo := (368813894857336493711/100000000000000000000)
  directionHi := (23050868428583530857/6250000000000000000)

def endpointA : IntegerEndpointWitness 180 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree180.table
  base := (-6800761926215453368598159510017054442423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-42527681338120789100720743680000000000000)
      constant := (915778811909717650965916703559931782230308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 180 interval.damping) (curvature.centralUpper 180 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree180.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 180 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree180.table
  base := (-1360152386112790058431739297125539991499/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2680324333117742691481866315600000000000000)
      constant := (59489045323811879319326431305021213510413725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 180 interval.damping) (curvature.centralUpper 180 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree180.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 180 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 180 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel181
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (368813894857336493711/100000000000000000000)
  centralHi := (23050868428583530857/6250000000000000000)
  directionLo := (184921333218449941669/50000000000000000000)
  directionHi := (369842666436899883339/100000000000000000000)

def endpointA : IntegerEndpointWitness 181 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree181.table
  base := (-421771432993286984369258024249004260599/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-42767376103701247383459539760000000000000)
      constant := (926650370083236852001199363478063727321664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 181 interval.damping) (curvature.centralUpper 181 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree181.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 181 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree181.table
  base := (-1687085732927950257171159597206766874169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2695425103349311563294410468640000000000000)
      constant := (60193055763219277150205953982425368463314380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 181 interval.damping) (curvature.centralUpper 181 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree181.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 181 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 181 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel182
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184921333218449941669/50000000000000000000)
  centralHi := (369842666436899883339/100000000000000000000)
  directionLo := (370868584264660417643/100000000000000000000)
  directionHi := (92717146066165104411/25000000000000000000)

def endpointA : IntegerEndpointWitness 182 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree182.table
  base := (-6695036736296683276244726797598442049201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-43007070869281705666198335840000000000000)
      constant := (937585400721243355027060204289606231803196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 182 interval.damping) (curvature.centralUpper 182 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree182.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 182 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree182.table
  base := (-3347518369825465288375111159726638620101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-387217981940125776443850660240000000000000)
      constant := (8700166660023602156634090408515135296592930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 182 interval.damping) (curvature.centralUpper 182 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree182.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 182 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 182 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel183
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370868584264660417643/100000000000000000000)
  centralHi := (92717146066165104411/25000000000000000000)
  directionLo := (371891671958099994799/100000000000000000000)
  directionHi := (929729179895249987/250000000000000000)

def endpointA : IntegerEndpointWitness 183 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree183.table
  base := (-6640843373394120764545653411984256994559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-43246765634862163948937131920000000000000)
      constant := (948583903735871588775748431302062972021764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 183 interval.damping) (curvature.centralUpper 183 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree183.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 183 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree183.table
  base := (-3320421688169963505359259607790403590253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2725626643812449306919498774720000000000000)
      constant := (61613377889269839079805515556734702240776030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 183 interval.damping) (curvature.centralUpper 183 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree183.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 183 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 183 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel184
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (371891671958099994799/100000000000000000000)
  centralHi := (929729179895249987/250000000000000000)
  directionLo := (186455976405362635473/50000000000000000000)
  directionHi := (372911952810725270947/100000000000000000000)

def endpointA : IntegerEndpointWitness 184 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree184.table
  base := (-6585762860859638020796159632361082207469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-43486460400442622231675928000000000000000)
      constant := (959645879040422618023323038910555671170124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 184 interval.damping) (curvature.centralUpper 184 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree184.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 184 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree184.table
  base := (-6585762863446664648369759932513602663359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2740727414044018178732042927760000000000000)
      constant := (62329689565224519892450445514262167347477045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 184 interval.damping) (curvature.centralUpper 184 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree184.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 184 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 184 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel185
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186455976405362635473/50000000000000000000)
  centralHi := (372911952810725270947/100000000000000000000)
  directionLo := (93482362449563889843/25000000000000000000)
  directionHi := (373929449798255559373/100000000000000000000)

def endpointA : IntegerEndpointWitness 185 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree185.table
  base := (-6529795220081867705661076004410103906979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-43726155166023080514414724080000000000000)
      constant := (970771326549341912127124704932359584372084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 185 interval.damping) (curvature.centralUpper 185 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree185.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 185 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree185.table
  base := (-6529795222353747660395303496219814757803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2755828184275587050544587080800000000000000)
      constant := (63050101642790519512554039770826145384338265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 185 interval.damping) (curvature.centralUpper 185 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree185.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 185 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 185 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel186
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93482362449563889843/25000000000000000000)
  centralHi := (373929449798255559373/100000000000000000000)
  directionLo := (374944185584659597449/100000000000000000000)
  directionHi := (7498883711693191949/2000000000000000000)

def endpointA : IntegerEndpointWitness 186 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree186.table
  base := (-6472940472168744209050628832626429713143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-43965849931603538797153520160000000000000)
      constant := (981960246178197733527512524149494281147428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 186 interval.damping) (curvature.centralUpper 186 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree186.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 186 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree186.table
  base := (-202279389817619139666545720150422523259/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2770928954507155922357131233840000000000000)
      constant := (63774614116797692016595391607588687417649440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 186 interval.damping) (curvature.centralUpper 186 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree186.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 186 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 186 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel187
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374944185584659597449/100000000000000000000)
  centralHi := (7498883711693191949/2000000000000000000)
  directionLo := (375956182528045668477/100000000000000000000)
  directionHi := (187978091264022834239/50000000000000000000)

def endpointA : IntegerEndpointWitness 187 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree187.table
  base := (-1603799659488189726630302752970938803551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-44205544697183997079892316240000000000000)
      constant := (993212637843660116722260924982464979143184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 187 interval.damping) (curvature.centralUpper 187 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree187.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 187 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree187.table
  base := (-3207599319852347326368806149259938763493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2786029724738724794169675386880000000000000)
      constant := (64503226982143217688070984463094630005888430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 187 interval.damping) (curvature.centralUpper 187 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree187.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 187 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 187 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel188
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (375956182528045668477/100000000000000000000)
  centralHi := (187978091264022834239/50000000000000000000)
  directionLo := (376965462686409409011/100000000000000000000)
  directionHi := (94241365671602352253/25000000000000000000)

def endpointA : IntegerEndpointWitness 188 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree188.table
  base := (-1589142434499018642684842961935295102179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-44445239462764455362631112320000000000000)
      constant := (1004528501463480410620703710209035278365136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 188 interval.damping) (curvature.centralUpper 188 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree188.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 188 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree188.table
  base := (-635656973953446566477611872225232282229/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2801130494970293665982219539920000000000000)
      constant := (65235940233790369020712508308440180908538950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 188 interval.damping) (curvature.centralUpper 188 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree188.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 188 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 188 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel189
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376965462686409409011/100000000000000000000)
  centralHi := (94241365671602352253/25000000000000000000)
  directionLo := (11811626494476358809/3125000000000000000)
  directionHi := (377972047823243481889/100000000000000000000)

def endpointA : IntegerEndpointWitness 189 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree189.table
  base := (-6297053792595505176583776788592190905963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-44684934228344913645369908400000000000000)
      constant := (1015907836956471359323326218035631236376148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 189 interval.damping) (curvature.centralUpper 189 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree189.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 189 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree189.table
  base := (-629705379394634433075080374194624992903/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-402318752171694648256394813280000000000000)
      constant := (9424679123823901057474290984895881252483950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 189 interval.damping) (curvature.centralUpper 189 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree189.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 189 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 189 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel190
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11811626494476358809/3125000000000000000)
  centralHi := (377972047823243481889/100000000000000000000)
  directionLo := (75795191882602630171/20000000000000000000)
  directionHi := (47371994926626643857/12500000000000000000)

def endpointA : IntegerEndpointWitness 190 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree190.table
  base := (-389790676361710428808627635227652413733/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-44924628993925371928108704480000000000000)
      constant := (1027350644242487698282593983145430245521088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 190 interval.damping) (curvature.centralUpper 190 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree190.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 190 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree190.table
  base := (-6236650822973487745976723315363888466091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2831332035433431409607307846000000000000000)
      constant := (66713667876165909344541381510935847325807705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 190 interval.damping) (curvature.centralUpper 190 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree190.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 190 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 190 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel191
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75795191882602630171/20000000000000000000)
  centralHi := (47371994926626643857/12500000000000000000)
  directionLo := (189988609323250827033/50000000000000000000)
  directionHi := (379977218646501654067/100000000000000000000)

def endpointA : IntegerEndpointWitness 191 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree191.table
  base := (-6175360845352205371111672267759848710349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-45164323759505830210847500560000000000000)
      constant := (1038856923242407244509268988358960605158604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 191 interval.damping) (curvature.centralUpper 191 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree191.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 191 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree191.table
  base := (-6175360846393665918859010941512339329803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2846432805665000281419851999040000000000000)
      constant := (67458682257140621195317284451177476864198265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 191 interval.damping) (curvature.centralUpper 191 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree191.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 191 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 191 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel192
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189988609323250827033/50000000000000000000)
  centralHi := (379977218646501654067/100000000000000000000)
  directionLo := (95243961609007285137/25000000000000000000)
  directionHi := (380975846436029140549/100000000000000000000)

def endpointA : IntegerEndpointWitness 192 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree192.table
  base := (-6113183882819404953100414476700046718959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-45404018525086288493586296640000000000000)
      constant := (1050426673878112461019368244173199813124164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 192 interval.damping) (curvature.centralUpper 192 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree192.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 192 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree192.table
  base := (-3056591941866912117430011141157949021469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2861533575896569153232396152080000000000000)
      constant := (68207797004907341335209468577824604979480190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 192 interval.damping) (curvature.centralUpper 192 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree192.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 192 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 192 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel193
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95243961609007285137/25000000000000000000)
  centralHi := (380975846436029140549/100000000000000000000)
  directionLo := (95492965855137201461/25000000000000000000)
  directionHi := (76394372684109761169/20000000000000000000)

def endpointA : IntegerEndpointWitness 193 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree193.table
  base := (-3025059976735841643632029258035942906021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-45643713290666746776325092720000000000000)
      constant := (1062059896072472477091452591685712456751832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 193 interval.damping) (curvature.centralUpper 193 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree193.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 193 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree193.table
  base := (-6050119954274537579536884980714723491229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2876634346128138025044940305120000000000000)
      constant := (68961012114742328917256437618356892744648895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 193 interval.damping) (curvature.centralUpper 193 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree193.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 193 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 193 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel194
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95492965855137201461/25000000000000000000)
  centralHi := (76394372684109761169/20000000000000000000)
  directionLo := (38296528997062374003/10000000000000000000)
  directionHi := (382965289970623740031/100000000000000000000)

def endpointA : IntegerEndpointWitness 194 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree194.table
  base := (-5986169076349476770031259998258936033329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-45883408056247205059063888800000000000000)
      constant := (1073756589749325547139807408446964255866684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 194 interval.damping) (curvature.centralUpper 194 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree194.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 194 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree194.table
  base := (-598616907705435974240888812222809091709/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2891735116359706896857484458160000000000000)
      constant := (69718327581981138263025965746822117725312950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 194 interval.damping) (curvature.centralUpper 194 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree194.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 194 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 194 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel195
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38296528997062374003/10000000000000000000)
  centralHi := (382965289970623740031/100000000000000000000)
  directionLo := (383956146193287883211/100000000000000000000)
  directionHi := (95989036548321970803/25000000000000000000)

def endpointA : IntegerEndpointWitness 195 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree195.table
  base := (-5921331270255220161638502557539595086919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-46123102821827663341802684880000000000000)
      constant := (1085516754833461932123486759919841619652324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 195 interval.damping) (curvature.centralUpper 195 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree195.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 195 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree195.table
  base := (-1184266254174814305250851727521969655707/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2906835886591275768670028611200000000000000)
      constant := (70479743402017578075837387365185587171758925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 195 interval.damping) (curvature.centralUpper 195 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree195.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 195 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 195 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel196
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383956146193287883211/100000000000000000000)
  centralHi := (95989036548321970803/25000000000000000000)
  directionLo := (384944451936794369921/100000000000000000000)
  directionHi := (192472225968397184961/50000000000000000000)

def endpointA : IntegerEndpointWitness 196 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree196.table
  base := (-1463901638439381092110629310364698217317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-46362797587408121624541480960000000000000)
      constant := (1097340391250607188417063721914164828522928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 196 interval.damping) (curvature.centralUpper 196 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree196.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 196 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree196.table
  base := (-5855606554300830806637092665340718737187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (598)
      previous := (207)
      next := (0)
      square := (4194658397658019947928931400000000000000)
      linear := (-417419522403263520068938966320000000000000)
      constant := (10177894224328956382311071274217074844198455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 196 interval.damping) (curvature.centralUpper 196 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree196.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 196 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 196 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel197
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (384944451936794369921/100000000000000000000)
  centralHi := (192472225968397184961/50000000000000000000)
  directionLo := (385930226795254434657/100000000000000000000)
  directionHi := (192965113397627217329/50000000000000000000)

def endpointA : IntegerEndpointWitness 197 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree197.table
  base := (-2894497472597627950312704214147901745269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-46602492352988579907280277040000000000000)
      constant := (1109227498927405849979809876916816786037848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 197 interval.damping) (curvature.centralUpper 197 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree197.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 197 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree197.table
  base := (-5788994945672227621809992211093170251261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2937037427054413512295116917280000000000000)
      constant := (72014876082343778504674412918434173288441055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 197 interval.damping) (curvature.centralUpper 197 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree197.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 197 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 197 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel198
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (385930226795254434657/100000000000000000000)
  centralHi := (192965113397627217329/50000000000000000000)
  directionLo := (386913490113169945683/100000000000000000000)
  directionHi := (96728372528292486421/25000000000000000000)

def endpointA : IntegerEndpointWitness 198 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree198.table
  base := (-715187057835190167451602781052345422373/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-46842187118569038190019073120000000000000)
      constant := (1121178077791405490486022640406324946484064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 198 interval.damping) (curvature.centralUpper 198 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree198.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 198 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree198.table
  base := (-715187057887530902766209752833203088977/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2952138197285982384107661070320000000000000)
      constant := (72788592933703393174990732778718921945605080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 198 interval.damping) (curvature.centralUpper 198 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree198.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 198 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 198 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell000.Kernel199
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386913490113169945683/100000000000000000000)
  centralHi := (96728372528292486421/25000000000000000000)
  directionLo := (96973565247465633293/25000000000000000000)
  directionHi := (387894260989862533173/100000000000000000000)

def endpointA : IntegerEndpointWitness 199 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree199.table
  base := (-565311112410755996174339375720636934269/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (69)
      previous := (23)
      next := (0)
      square := (479389531160916565477592160000000000000)
      linear := (-47081881884149496472757869200000000000000)
      constant := (1133192127771041152830347472161174522629240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 199 interval.damping) (curvature.centralUpper 199 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree199.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 199 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree199.table
  base := (-1413277781118785967291057221426125718119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4186)
      previous := (1449)
      next := (0)
      square := (29362608783606139635502519800000000000000)
      linear := (-2967238967517551255920205223360000000000000)
      constant := (73566410119998426393042279197890396796243380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 199 interval.damping) (curvature.centralUpper 199 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree199.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 199 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 199 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell000.Kernel199
