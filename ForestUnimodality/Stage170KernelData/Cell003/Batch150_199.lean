import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell003.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch150_199
import ForestUnimodality.BinomialMassData.Q9_35.Batch150_199

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel150
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
  base := (-2079534776482005521773870212438778098493/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-25977722650568726980857547980000000000000)
      constant := (445155078955553828470931620225979550424112) }

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
  base := (-8318140194605504861480823800005636820503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1637404295655593586440723634300000000000000)
      constant := (28995323216446114489487071527498618978976765) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel151
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
  base := (-8325346436016577428557417412623347259583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-26153984682219237681288781582000000000000)
      constant := (451642713051798102687852165169756610961668) }

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
  base := (-2081336844837560537353764998854617992223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1648508803649575760567891351226000000000000)
      constant := (29416031997522889912844291300618674367621460) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel152
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
  base := (-416604565124755060303284584541096791371/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-26330246713869748381720015184000000000000)
      constant := (458176262510395130835695167652712256690320) }

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
  base := (-1041511514981825312868197633955097161551/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1659613311643557934695059068152000000000000)
      constant := (29839709522351295958477407262292809563360040) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel153
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
  base := (-8338373750636646897441449200132831772571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-26506508745520259082151248786000000000000)
      constant := (464755727150252699003176045611718672909716) }

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
  base := (-8338374458815307481084987740443348090879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1670717819637540108822226785078000000000000)
      constant := (30266355780470635844428332238137179717734645) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel154
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
  base := (-8344193824337219016805267125569898843173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-26682770777170769782582482388000000000000)
      constant := (471381106795786789133812490306720404627308) }

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
  base := (-4172097218946985827788813132266655011291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-240260332518788897564199214572000000000000)
      constant := (4385138680239116285802814484826934149209630) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel155
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
  base := (-4174775783116691852223313251689455064781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-26859032808821280483013715990000000000000)
      constant := (478052401276451136666446577592734359481752) }

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
  base := (-8349552097789436268406734969185280991483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1692926835625504457076562218930000000000000)
      constant := (31128554455989614322765621339554606157086665) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel156
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
  base := (-8354447017805137214529816029383689349917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-27035294840471791183444949592000000000000)
      constant := (484769610426325756584421152686465242600332) }

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
  base := (-8354447478301340266980249829396980876221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1704031343619486631203729935856000000000000)
      constant := (31564106853667125268751147761560939685325855) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel157
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
  base := (-167177604389320557480194707058315965969/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-27211556872122301883876183194000000000000)
      constant := (491532734083756455579916616990586806806200) }

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
  base := (-8358880618386136917229575918572166941881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1715135851613468805330897652782000000000000)
      constant := (32002627945162015788423086416823619099239155) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel158
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
  base := (-836285121064225295746633429407844013571/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-27387818903772812584307416796000000000000)
      constant := (498341772091038444554613171224686239457160) }

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
  base := (-8362851556206593407528141338100040556239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1726240359607450979458065369708000000000000)
      constant := (32444117721124407920629947420502290063721445) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel159
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
  base := (-8366360029842215566386302196539879575949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-27564080935423323284738650398000000000000)
      constant := (505196724294138111102564058014090481696204) }

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
  base := (-8366360329175664328237612812354127741237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1737344867601433153585233086634000000000000)
      constant := (32888576172388127790733122425125438703396935) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel160
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
  base := (-1673881342943564561984727214799531298929/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-27740342967073833985169884000000000000000)
      constant := (512097590542447826787153289304009374021420) }

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
  base := (-8369406973995504194631068946205611679137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1748449375595415327712400803560000000000000)
      constant := (33336003289961147542490707172499625138611435) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel161
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
  base := (-4185995651059315433594008446113722570449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-27916604998724344685601117602000000000000)
      constant := (519044370688569366891942141231340219436408) }

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
  base := (-4185995763346138158173386841615523137547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-251364840512771071691366931498000000000000)
      constant := (4826628437859579595005903856635513380371710) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel162
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
  base := (-4187056914069895499085917670113059346617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-28092867030374855386032351204000000000000)
      constant := (526037064588122126376961051040095525227064) }

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
  base := (-167482280452946455337539723139999296639/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1770658391583379675966736237412000000000000)
      constant := (34239763488887427850379378409247808616172250) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel163
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
  base := (-8375774328164619924212225384267542664909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-28269129062025366086463584806000000000000)
      constant := (533075672099572838356861482865179829340364) }

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
  base := (-261742953019536899828416613768703875363/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1781762899577361850093903954338000000000000)
      constant := (34696096553054947972674393218991161617154080) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel164
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
  base := (-8376972836902505342572109338649307172149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-28445391093675876786894818408000000000000)
      constant := (540160193084083952042591747449402771311404) }

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
  base := (-4188486491399431437025351113649522842049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1792867407571344024221071671264000000000000)
      constant := (35155398249147229475598682862826933807395990) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel165
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
  base := (-4188854694211380096580655969623797719127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-28621653125326387487326052010000000000000)
      constant := (547290627405378215674512545849259618246984) }

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
  base := (-167554190295455182489496268522192027449/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1803971915565326198348239388190000000000000)
      constant := (35617668568931196780003687041048147663749750) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel166
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
  base := (-2094496004046238880045365261136268419381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-28797915156976898187757285612000000000000)
      constant := (554466974929617345075817366630819705289904) }

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
  base := (-1047248015700433829592123489506402347159/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1815076423559308372475407105116000000000000)
      constant := (36082907504307982618605351697294651399568360) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel167
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
  base := (-8377796753066189524490422816665218230383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-28974177188627408888188519214000000000000)
      constant := (561689235525292947443074745145589127078468) }

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
  base := (-8377796847818839189686531508041677884463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1826180931553290546602574822042000000000000)
      constant := (36551115047308265755585596907891588918306565) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel168
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
  base := (-4188573815692844047127511658603985708781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-29150439220277919588619752816000000000000)
      constant := (568957409063128119223617377147168114329752) }

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
  base := (-8377147713435401868597162814357522316113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-262469348506753245818534648424000000000000)
      constant := (5288898741441142086436051658975886718936045) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel169
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
  base := (-8376036682927078362294267782380507309521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-29326701251928430289050986418000000000000)
      constant := (576271495415988351886169241690727970761916) }

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
  base := (-8376036753974467373099231593319494991793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1848389947541254894856910255894000000000000)
      constant := (37496435924924448535596210121324923727010715) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel170
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
  base := (-8374463938958630486993759229656717303047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-29502963283578940989482220020000000000000)
      constant := (583631494458800564797187926706373130787812) }

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
  base := (-8374464000476983564729263324138947778143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1859494455535237068984077972820000000000000)
      constant := (37973549244212595321140693690965957794354965) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel171
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
  base := (-8372429430251722871837407243605712728561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-29679225315229451689913453622000000000000)
      constant := (591037406068479244342737793855827149085756) }

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
  base := (-8372429483517342420820922249862292960591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1870598963529219243111245689746000000000000)
      constant := (38453631140461708927239064582207938224655205) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel172
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
  base := (-2092483296774437887113244231215787235797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-29855487346879962390344687224000000000000)
      constant := (598489230123858806396307782736547404227248) }

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
  base := (-8369933233216248483281861871451105857317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1881703471523201417238413406672000000000000)
      constant := (38936681606292216741123947687315279064957335) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel173
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
  base := (-167339504786473493859130886054853329499/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-30031749378530473090775920826000000000000)
      constant := (605986966505631418253433589231279334100200) }

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
  base := (-2091743819813189912087397447818225376513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1892807979517183591365581123598000000000000)
      constant := (39422700634432749578217153643707939131017260) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel174
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
  base := (-8363555616306357572809896172014031122143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-30208011410180983791207154428000000000000)
      constant := (613530615096289618844268066160943875511428) }

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
  base := (-20908889127188985834273074998539009369/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1903912487511165765492748840524000000000000)
      constant := (39911688217717371426185827073814377081838000) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel175
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
  base := (-8359674346985861069054136403120063163949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-30384273441831494491638388030000000000000)
      constant := (621120175780073164644646798043769747344204) }

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
  base := (-4179837188456893168458171691927024913553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-273573856500735419945702365350000000000000)
      constant := (5771949192726138429232693651440108256051290) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel176
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
  base := (-4177665729938898900799116230760201891227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-30560535473482005192069621632000000000000)
      constant := (628755648442919605174933915017918384870184) }

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
  base := (-334213259431470310691661465828406022291/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1926121503499130113747084274376000000000000)
      constant := (40898569021566783896762690460732213113467625) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel177
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
  base := (-8350526983084863385395459104179015509287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-30736797505132515892500855234000000000000)
      constant := (636437032972418157975316318055533937962852) }

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
  base := (-8350527005513871038262294746824553031123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1937226011493112287874251991302000000000000)
      constant := (41396462228304072311297597960117784507374865) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel178
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
  base := (-8345260944307636102285656083517845049529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-30913059536783026592932088836000000000000)
      constant := (644164329257766509918434648146928619801884) }

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
  base := (-8345260963723512830249405869660921787913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1948330519487094462001419708228000000000000)
      constant := (41897323962525879511530484953533874161961315) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel179
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
  base := (-8339533370854725976441052703913053013107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-31089321568433537293363322438000000000000)
      constant := (651937537189730220907599988074597787947572) }

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
  base := (-4169766693830877994331342397702972404343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1959435027481076636128587425154000000000000)
      constant := (42401154217556917650335946819589743521871930) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel180
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
  base := (-4166672144826171811402709347283340224919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-31265583600084047993794556040000000000000)
      constant := (659756656660604448483037258921733278200648) }

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
  base := (-520834019012539959177562062491352418733/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1970539535475058810255755142080000000000000)
      constant := (42907952986813537213545962496713898518566640) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel181
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
  base := (-1665338745450670013355874496281396451673/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-31441845631734558694225789642000000000000)
      constant := (667621687564177748543143986984622070966540) }

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
  base := (-33306774959384401288955332092928596623/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-1981644043469040984382922859006000000000000)
      constant := (43417720263801783533884178862556323456841250) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel182
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
  base := (-8319581709845840810558499626161310536711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-31618107663385069394657023244000000000000)
      constant := (675532629795697739079137830016354757853156) }

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
  base := (-8319581720745590707721920628926184856447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-284678364494717594072870082276000000000000)
      constant := (6275779434587932988871213650725983530024355) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel183
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
  base := (-166240165265226211507670791693746513123/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-31794369695035580095088256846000000000000)
      constant := (683489483251838441206055830193500697375400) }

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
  base := (-8312008272695402267257863638928946028803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2003853059457005332637258292858000000000000)
      constant := (44446160315434687896016848657904208222943265) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel184
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
  base := (-1660794682596487846289622289122405712993/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-31970631726686090795519490448000000000000)
      constant := (691492247830669135443123511161551885740140) }

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
  base := (-8303973421147725459615565852471864249807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2014957567450987506764426009784000000000000)
      constant := (44964833077523467793240856740211593258797285) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel185
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
  base := (-8295477184150534310845164012753447963663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-32146893758336601495950724050000000000000)
      constant := (699540923431624591661969077705236208145348) }

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
  base := (-8295477191217461780495930290035683822083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2026062075444969680891593726710000000000000)
      constant := (45486474322228719747323798561986257463589665) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel186
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
  base := (-4143259800786330536805848461677445779501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-32323155789987112196381957652000000000000)
      constant := (707635509955476548822444531275580433763992) }

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
  base := (-1657303921537761553754713266836661761871/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2037166583438951855018761443636000000000000)
      constant := (46011084043478315606241394824500289341708025) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel187
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
  base := (-8277100689728487267914671294513933778419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-32499417821637622896813191254000000000000)
      constant := (715776007304306335931882027404194264886324) }

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
  base := (-1655420139004325322299910498413593240599/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2048271091432934029145929160562000000000000)
      constant := (46538662235279588889166131293501148280266225) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel188
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
  base := (-8267220472776866410818689956630275221481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-32675679853288133597244424856000000000000)
      constant := (723962415381478538922023154769478899114076) }

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
  base := (-4133610238678810728918660042802762701149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2059375599426916203273096877488000000000000)
      constant := (47069208891717822324552967295119446276436990) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel189
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
  base := (-165137579491243610910006233485225885891/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-32851941884938644297675658458000000000000)
      constant := (732194734091615629620161678313204822821800) }

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
  base := (-1032109872315790371742302650017631523007/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-295782872488699768200037799202000000000000)
      constant := (6800389143850682985599253224063663173558040) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel190
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
  base := (-4123038109310230471649030012693046647691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-33028203916589154998106892060000000000000)
      constant := (740472963340573482940943503723455626818472) }

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
  base := (-824607622205090230415608544120424357471/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2081584615414880551527432311340000000000000)
      constant := (48139207575227287682725005860124960324196050) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel191
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
  base := (-8234812228185303062293749074741008542521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-33204465948239665698538125662000000000000)
      constant := (748797103035417717052041374741285965829916) }

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
  base := (-8234812231153819419340115604166823613979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2092689123408862725654600028266000000000000)
      constant := (48678659590845839982285465485291328214575145) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel192
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
  base := (-822308702619359020295538957398777583493/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-33380727979890176398969359264000000000000)
      constant := (757167153084400798751583248360048896660280) }

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
  base := (-8223087028762315804718020826443082668031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2103793631402844899781767745192000000000000)
      constant := (49221080048193263633995411705278244746332405) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel193
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
  base := (-1026362579411379834585407958841013290631/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-33556990011540687099400592866000000000000)
      constant := (765583113396939862793967995989337574699808) }

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
  base := (-64147661230576246453932671883880761939/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2114898139396827073908935462118000000000000)
      constant := (49766468941723403456830517201275299305592960) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel194
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
  base := (-2049563269459393972866519344379404555027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-33733252043191197799831826468000000000000)
      constant := (774044983883595199547240793578929527119568) }

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
  base := (-1639650615952170019061845651491790630797/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2126002647390809248036103179044000000000000)
      constant := (50314826265959848085096589836625756477273675) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel195
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
  base := (-8185144375912561530964731413944046693937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-33909514074841708500263060070000000000000)
      constant := (782552764456049370276758038250473813224252) }

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
  base := (-8185144377576689317257945606176731221863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2137107155384791422163270895970000000000000)
      constant := (50866152015494687561887645038691700850643565) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel196
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
  base := (-65372596410558887476393223774016995607/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-34085776106492219200694293672000000000000)
      constant := (791106455027086913625040021236991502196500) }

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
  base := (-81715745527597248289021594004503193871/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-306887380482681942327205516128000000000000)
      constant := (7345778026426757460150041370849838821451500) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel197
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
  base := (-509846476599548678388620189496713370869/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-34262038138142729901125527274000000000000)
      constant := (799706055510574610584092418614460344264384) }

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
  base := (-8157543626838571121502734822308750242203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2159316171372755770417606329822000000000000)
      constant := (51977708769163181512225611538800156190660265) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel198
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
  base := (-8143051619998860951559339069763153214803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-34438300169793240601556760876000000000000)
      constant := (808351565821442278507562040481947387140788) }

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
  base := (-325722064843068540123791660478626234009/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2170420679366737944544774046748000000000000)
      constant := (52537939762812771534945006555393214316694875) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel199
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
  base := (-508006159721535605486638030956359740121/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-34614562201443751301987994478000000000000)
      constant := (817042985875664067550597657199042976632256) }

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
  base := (-4064049278238549749115899303409654248049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2181525187360720118671941763674000000000000)
      constant := (53101139160790350145692874707065469418455990) }

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
end ForestUnimodality.Stage170KernelData.Cell003.Kernel199
