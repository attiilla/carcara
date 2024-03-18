SMT2_FILES := $(shell find ./sample -type f -name "*.smt2")
#echo "Condition is true";\
#echo "Condition is false";\
#echo "$$(head -n 1 $$file.proof.compressed | awk '{print $$1}')";\

compress:
	@count=0; \
	correct=0; \
	for file in $(SMT2_FILES); do \
		./target/debug/carcara compress --ignore-unknown-rules --allow-int-real-subtyping $$file.proof $$file > $$file.proof.compressed; \
		if [ "$$(head -n 1 $$file.proof.compressed | awk '{print $$1}')" = "Error" ]; then\
			rm "$$file.proof.compressed";\
		else\
			count=$$((count + 1));\
			validity=$$(./target/debug/carcara check --ignore-unknown-rules --allow-int-real-subtyping $$file.proof $$file);\
			if [ "$$validity" = "valid" ]; then\
				correct=$$((correct + 1));\
			fi; \
		fi; \
	done; \
	echo "Compressable $$count";\
	echo "Correct $$correct"

list:
	for file in $(SMT2_FILES); do \
		echo "$$file and $$file.proof"; \
	done
