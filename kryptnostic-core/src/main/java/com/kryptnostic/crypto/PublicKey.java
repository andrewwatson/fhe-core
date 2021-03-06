package com.kryptnostic.crypto;

import java.nio.ByteBuffer;
import java.util.Random;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.common.base.Preconditions;
import com.kryptnostic.crypto.padding.PaddingStrategy;
import com.kryptnostic.crypto.padding.ZeroPaddingStrategy;
import com.kryptnostic.multivariate.PolynomialFunctionGF2;
import com.kryptnostic.multivariate.gf2.SimplePolynomialFunction;

import cern.colt.bitvector.BitVector;

/**
 * Public key class used for encryption. 
 * @author Matthew Tamayo-Rios
 */
public class PublicKey {
    private static final Logger logger = LoggerFactory.getLogger( PublicKey.class );
    //TODO: Replace with bouncy castle or real number generator.
    private static final Random r = new Random( 0 );
    private final SimplePolynomialFunction encrypter;
    private final PolynomialFunctionGF2 m;
    private final PaddingStrategy paddingStrategy;
    private final int longsPerBlock;
    public PublicKey( PrivateKey privateKey ) {
        this( privateKey, new ZeroPaddingStrategy( privateKey.getE1().rows() >>> 4 ) );
    }
    public PublicKey( PrivateKey privateKey , PaddingStrategy paddingStrategy ) {
        this.paddingStrategy = paddingStrategy;
        int inputLen =  privateKey.getE1().cols();
        int outputLen = privateKey.getE1().rows();
        m = PolynomialFunctionGF2.truncatedIdentity( inputLen , outputLen );
        logger.debug( "m: {} -> {}" , inputLen , outputLen );
        
        /*
         * E(m) = E1(m + F( R(m,r)) ) + E2(R(m,r))
         */
        
        encrypter = privateKey.encrypt( m ); 
        logger.debug("Required input length in bits: {}" , encrypter.getInputLength() );
        // 8 bits per byte, 8 bytes per long.
        longsPerBlock = encrypter.getInputLength() >>> 7;
    }
    
    public Ciphertext encryptIntoEnvelope( byte[] plaintext ) {
        long[] lengthArray = new long[ longsPerBlock<<1 ];
        
        lengthArray[0] = plaintext.length;
        for( int i = 1 ; i < lengthArray.length ; ++i ) {
            lengthArray[ i ] = r.nextLong();
        }
        
        return new Ciphertext( encrypt( plaintext ) , encrypt( lengthArray ) );
    }
    
    public byte[] encrypt( byte[] plaintext ) {
        Preconditions.checkNotNull( plaintext , "Plaintext to be encrypted cannot be null." );
        
        /* 
         * 1) Pad the data so it aligns 
         */
        plaintext = paddingStrategy.pad( plaintext );
               
        ByteBuffer buffer = ByteBuffer.wrap( plaintext );
        ByteBuffer outBuf = ByteBuffer.allocate( plaintext.length << 1 );
        
        int blockLen = longsPerBlock << 1;
        while( buffer.remaining() > 0 ) {
            long[] lpt = new long[ blockLen ];
            
            for( int i = 0 ; i < longsPerBlock; ++i ) {
               lpt[i] = buffer.getLong();
            }
            
            for( int i = longsPerBlock; i < blockLen ; ++i ) {
               lpt[i] = 0L;//r.nextLong();
            }
            
            long[] ciphertext = encrypt( lpt );
            for( long lct : ciphertext ) {
                outBuf.putLong( lct );
            }
        }
        
        return outBuf.array();
    }
    
    public long[] encrypt( long[] plaintext ) {
        logger.debug( "Expected plaintext block length: {}" , encrypter.getInputLength() );
        logger.debug( "Observed plaintext block length: {}" , plaintext.length * 8 * 8 );
        Preconditions.checkArgument( (plaintext.length<<3) == ( encrypter.getInputLength() >>> 3 ) , "Cannot directly encrypt block of incorrect length." );
        
        BitVector result = encrypter.apply( new BitVector( plaintext , encrypter.getInputLength() ) );
        for( long l : result.elements() ) {
            logger.debug("Wrote the following ciphertext long: {}" , l );
        }
        return result.elements();
    }
    
    //public abstract byte[] encryptObject( Object object );
    
    public SimplePolynomialFunction getEncrypter() {
        return encrypter;
    }

    public PolynomialFunctionGF2 getM() {
        return m;
    }
}
