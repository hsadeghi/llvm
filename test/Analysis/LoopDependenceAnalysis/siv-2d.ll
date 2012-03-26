@a = external global [256 x [256 x i32]]

;; for (i = 0; i < 255; i++) {
;;   for (j = 1; j < 256; j++) {
;;     m0 = a[i][j];              // 0
;;     a[i - 1][j + 1] = m0 + 10; // 1
;;   }
;; }

define void @test() nounwind uwtable {
Entry:
  br label %Outer
Outer: ;; Preds: Entry, InnerFinish
  %i = phi i64 [0, %Entry], [ %i.plus.1, %InnerFinish ]
  %outerExitCond = icmp eq i64 %i, 255
  br i1 %outerExitCond, label %OuterFinish, label %Inner

Inner: ;; Preds: Outer, InnerBody
  %j = phi i64 [1, %Outer], [%j.plus.1, %InnerBody]
  %innerExitCond = icmp eq i64 %j, 256
  br i1 %innerExitCond, label %InnerFinish, label %InnerBody

InnerBody: ;; Preds Inner
  %i.minus.1 = sub nsw i64 %i, 1
  %j.plus.1 = add nsw i64 %j, 1

  %loadPtr  = getelementptr inbounds [256 x [256 x i32]]* @a, i64 0, i64 %i, i64 %j
  %storePtr = getelementptr inbounds [256 x [256 x i32]]* @a, i64 0,
              i64 %i.minus.1, i64 %j.plus.1
  %loadedValue = load i32* %loadPtr, align 4 ;; 0
  store i32 %loadedValue, i32* %storePtr, align 4 ;; 1
  br label %Inner

InnerFinish: ;; Preds InnerBody
  %i.plus.1 = add nsw i64 %i, 1
  br label %Outer

OuterFinish: ;; Preds InnerFinish
  ret void
}
