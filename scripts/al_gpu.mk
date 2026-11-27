# make -f al_gpu.mk -j4   (in a directory holding al_vec.c, al_gpu.h, al_gpu_host.c, al_gpu.cu)
NVCC ?= /usr/local/cuda/bin/nvcc
ARCH ?= sm_86
all: al_gpu al_s1ref
al_gpu_host.o: al_gpu_host.c al_vec.c al_gpu.h
	gcc -O3 -fopenmp -Wall -Wno-unused-function -c al_gpu_host.c -o $@
al_gpu: al_gpu.cu al_gpu.h al_gpu_host.o
	$(NVCC) -O3 -arch=$(ARCH) -Xcompiler -fopenmp al_gpu.cu al_gpu_host.o -o $@
al_s1ref: al_gpu_host.c al_vec.c al_gpu.h
	gcc -O3 -fopenmp -Wall -Wno-unused-function -DNOGPU al_gpu_host.c -o $@
al_vec: al_vec.c
	gcc -O2 -fopenmp -o $@ al_vec.c
