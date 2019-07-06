.PHONY: test
test:
	agda --safe Deduction.agda
	agda --safe Models.agda
