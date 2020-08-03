#include "stdlib.h"
#include "stdio.h"
#define xstrdup(a) strdup(a)
///home/cc/gcc/ins/bin/gcc  -fplugin=/home/cc/gcc/myfile/Compiler/misra.so -I/home/cc/gcc/ins/lib/gcc/x86_64-pc-linux-gnu/7.3.0/plugin/include openssl_df_2.c  -O1  -flto  -fno-tree-dse  -fno-tree-fre -fno-tree-dce -fipa-pta   -fno-inline-functions-called-once   -o  openssl_df_2.o 

int * foo(int z);
void boo(int *b){
	free(b);
	printf("asdda\n");
}
int main(){
	int *p;
	int *q=malloc(5);
	int n;
	scanf("%d",n);
	p=foo(2);
	if(n)
		free(p);
	else
		boo(p);
	q=p;
	free(q);
	printf("%d",q);
	return 0 ;
}

