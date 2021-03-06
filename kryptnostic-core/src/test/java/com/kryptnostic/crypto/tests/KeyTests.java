package com.kryptnostic.crypto.tests;

import org.apache.commons.lang3.StringUtils;
import org.junit.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.kryptnostic.crypto.Ciphertext;
import com.kryptnostic.crypto.PrivateKey;
import com.kryptnostic.crypto.PublicKey;
import com.kryptnostic.linear.EnhancedBitMatrix;
import com.kryptnostic.linear.EnhancedBitMatrix.SingularMatrixException;
import com.kryptnostic.multivariate.gf2.SimplePolynomialFunction;

import junit.framework.Assert;

public class KeyTests {
    private static final Logger logger = LoggerFactory.getLogger( KeyTests.class );
    private static final PrivateKey privKey = new PrivateKey( 128 , 64 );
    private static final PublicKey pubKey = new PublicKey( privKey );
    
    @Test
    public void testConstruction() throws SingularMatrixException {
        PrivateKey privKey = new PrivateKey( 128 , 64 );
        PublicKey pubKey = new PublicKey( privKey );
        logger.info("Finished generating key pair. Starting assumption tests...");

        SimplePolynomialFunction e = pubKey.getEncrypter();
        SimplePolynomialFunction DX = privKey.getD().multiply( e ); 
        SimplePolynomialFunction FofR = privKey.getF().compose( DX );
        EnhancedBitMatrix L = privKey.getE2().getLeftNullifyingMatrix();
        L = L.multiply( privKey.getE1() ).inverse().multiply( L );  //Normalize
        SimplePolynomialFunction mFofR = L.multiply( e );
        
        Assert.assertEquals( mFofR.xor( FofR ) , pubKey.getM() );
    }
    
    @Test 
    public void testEncryptDecrypt() throws SingularMatrixException {
        String plaintext = "hey!1234hey!1234hey!1234hey!12";
        byte[] plaintextBytes = plaintext.getBytes();
        byte[] ciphertext = pubKey.encrypt( plaintextBytes );
        logger.info( "Plaintext: {}", plaintext );
        logger.info( "Ciphertext: {}", new String( ciphertext ) );
        byte[] decryptedBytes = privKey.decrypt( ciphertext ); 
        String decryptedPlaintext = new String( decryptedBytes );
        logger.info( "Decrypted ciphertext: {}" , decryptedPlaintext );
        Assert.assertTrue( StringUtils.startsWith( decryptedPlaintext , plaintext ) );
    }
    
    @Test 
    public void testEncryptDecryptWithEnvelope() {
        String plaintext = "hey!1234hey!1234hey!1234hey!1";
        byte[] plaintextBytes = plaintext.getBytes();
        Ciphertext ciphertext = pubKey.encryptIntoEnvelope( plaintextBytes );
        byte[] decryptedBytes = privKey.decryptFromEnvelope( ciphertext ); 
        String decryptedPlaintext = new String( decryptedBytes );
        logger.info( "Decrypted ciphertext: {}" , decryptedPlaintext );
        Assert.assertEquals( decryptedPlaintext , plaintext );
    }
}
